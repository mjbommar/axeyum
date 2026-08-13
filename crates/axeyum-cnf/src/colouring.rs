//! Generic colouring-CNF encoding: forbid monochromatic solution sets.
//!
//! Ramsey-type numbers — Rado, Schur, van der Waerden — are all decided by the
//! same propositional question: *can `1..=points` be coloured with
//! `1..=colours` so that no solution of some relation is monochromatic?* The
//! relation is the only thing that varies, so this module has **one encoder**,
//! [`ColouringProblem::encode`], parameterised by a [`SolutionFamily`] that
//! supplies the solution sets. Nothing here is Rado-specific.
//!
//! # Why byte-identity matters here
//!
//! `scripts/gen-rado-instance.py` is the **generator of record** named by every
//! claim in `artifacts/claims/rado/`: it defines what those claims mean, and a
//! stored DRAT refutation only refutes the *intended* instance if the CNF
//! regenerates exactly. [`Rado`] reproduces that generator's output
//! **byte for byte** through [`ColouringProblem::to_dimacs`], and
//! `tests/colouring_encoding_parity.rs` is the differential gate that checks it
//! on every instance the ledger cites. Clause **order** is therefore part of the
//! public contract of this module, not an implementation detail.
//!
//! # Variable convention
//!
//! `v(j, i) = (j - 1) * colours + i`, one-based in DIMACS — "point `j` has
//! colour `i`". The **first `points` clauses** are the at-least-one clauses
//! `{v(j,1) … v(j,colours)}`, in ascending `j`; cube-cover arguments that split
//! on a point's colour depend on those clauses being present verbatim.
//!
//! # Clause groups, in emission order
//!
//! 1. **at-least-one** — every point gets a colour;
//! 2. **negative** — for each solution set and each colour, not all its members
//!    take that colour (the sets are consumed in the family's order, and each
//!    set's literals ascend by point);
//! 3. **at-most-one** — no point takes two colours;
//! 4. **symmetry breaking** — point 1 takes colour 1, and point `j` may take
//!    colour `i > 1` only if some `j' < j` takes colour `i - 1`, so colour
//!    classes are ordered by least element. Sound because colour names are
//!    interchangeable: every avoiding colouring renames into one satisfying it.
//!
//! Groups 3 and 4 are optional through [`EncodingOptions`]; the default is both
//! enabled, which is the generator-of-record profile.
//!
//! # Two implementations of every relation, on purpose
//!
//! A family supplies [`SolutionFamily::solution_sets`] (the fast enumeration the
//! encoder consumes) **and** [`SolutionFamily::first_violation`] (a brute-force
//! search written from the defining relation). A colouring accepted by the
//! enumeration that built the formula only proves the encoder agrees with
//! itself; a colouring accepted by an independent pass over the relation is
//! evidence. [`verify_colouring`] uses the second.
//!
//! # Example
//!
//! ```
//! use axeyum_cnf::colouring::{ColouringProblem, Schur, verify_colouring};
//!
//! // Schur: [1..4] has a 2-colouring with no monochromatic x + y = z.
//! let family = Schur;
//! let problem = ColouringProblem::from_family(&family, 4, 2)?;
//! let formula = problem.encode()?;
//! assert_eq!(formula.variable_count(), 8);
//!
//! verify_colouring(&family, &[1, 2, 2, 1], 2)?;
//! # Ok::<(), axeyum_cnf::colouring::ColouringError>(())
//! ```

use crate::{CnfClause, CnfError, CnfFormula, CnfLit, CnfVar};

/// Errors from building, encoding, or checking a colouring instance.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ColouringError {
    /// The CNF layer rejected a variable, literal, or clause.
    Cnf(CnfError),
    /// A parameter was outside the range this module accepts.
    InvalidParameter {
        /// What was wrong, in the caller's terms.
        what: String,
    },
    /// A point index was outside `1..=points`.
    PointOutOfRange {
        /// Offending point.
        point: usize,
        /// Number of points in the instance.
        points: usize,
    },
    /// A colour index was outside `1..=colours`.
    ColourOutOfRange {
        /// Offending colour.
        colour: usize,
        /// Number of colours in the instance.
        colours: usize,
    },
    /// A colouring covered the wrong number of points.
    ColouringLength {
        /// Points the instance has.
        expected: usize,
        /// Points the colouring covers.
        found: usize,
    },
    /// A model did not assign exactly one colour to a point.
    ModelNotOneHot {
        /// The point with zero or several colours.
        point: usize,
        /// How many colours the model gave it.
        colours: usize,
    },
    /// **The colouring is not a witness.** It makes a solution set
    /// monochromatic.
    Monochromatic {
        /// The offending set, ascending.
        members: Vec<usize>,
        /// The colour all its members share.
        colour: usize,
    },
}

impl core::fmt::Display for ColouringError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Cnf(error) => write!(f, "{error}"),
            Self::InvalidParameter { what } => write!(f, "invalid parameter: {what}"),
            Self::PointOutOfRange { point, points } => {
                write!(f, "point {point} outside 1..={points}")
            }
            Self::ColourOutOfRange { colour, colours } => {
                write!(f, "colour {colour} outside 1..={colours}")
            }
            Self::ColouringLength { expected, found } => {
                write!(
                    f,
                    "colouring covers {found} points, instance has {expected}"
                )
            }
            Self::ModelNotOneHot { point, colours } => {
                write!(
                    f,
                    "model gives point {point} {colours} colours, want exactly 1"
                )
            }
            Self::Monochromatic { members, colour } => {
                write!(f, "monochromatic {members:?}, all coloured {colour}")
            }
        }
    }
}

impl core::error::Error for ColouringError {}

impl From<CnfError> for ColouringError {
    fn from(error: CnfError) -> Self {
        Self::Cnf(error)
    }
}

/// Sorts and deduplicates a tuple's members into a solution set.
///
/// Solutions are forbidden as **sets**: `a(x-y) = bz` admits `z = x`, and the
/// clause then has two literals, not three.
fn member_set(members: &[usize]) -> Vec<usize> {
    let mut set = members.to_vec();
    set.sort_unstable();
    set.dedup();
    set
}

/// A relation whose monochromatic solutions a colouring must avoid.
///
/// Implementors supply two deliberately different derivations of the same
/// mathematics — see the [module docs](self#two-implementations-of-every-relation-on-purpose).
pub trait SolutionFamily {
    /// Short machine-readable name, e.g. `rado`.
    fn name(&self) -> &'static str;

    /// Human-readable identity, e.g. `4(x-y)=3z`.
    fn label(&self) -> String;

    /// The solution sets inside `1..=points`, each ascending and duplicate-free.
    ///
    /// The returned **order is part of the encoding contract**: the encoder
    /// emits negative clauses in exactly this order, and byte-identity with an
    /// external generator depends on it. Implementations must be deterministic.
    fn solution_sets(&self, points: usize) -> Vec<Vec<usize>>;

    /// The first monochromatic solution in `colouring`, found by brute force
    /// over the defining relation.
    ///
    /// `colouring[j - 1]` is the colour of point `j`. Implementations must
    /// **not** call [`SolutionFamily::solution_sets`]: the value of this method
    /// is that it shares no code with the encoder.
    fn first_violation(&self, colouring: &[usize]) -> Option<(Vec<usize>, usize)>;
}

/// Which optional clause groups an encoding emits.
///
/// Group order never varies; only presence does. [`EncodingOptions::default`]
/// enables both optional groups, which is the profile
/// `scripts/gen-rado-instance.py` emits and the one the claim ledger's stored
/// CNFs were produced with.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EncodingOptions {
    /// Emit group 3, at-most-one colour per point.
    ///
    /// Not needed for equisatisfiability; it makes models and colourings
    /// correspond one to one, so a model decodes without a tie-break.
    pub at_most_one: bool,
    /// Emit group 4, colour classes ordered by least element.
    pub symmetry_breaking: bool,
}

impl Default for EncodingOptions {
    fn default() -> Self {
        Self {
            at_most_one: true,
            symmetry_breaking: true,
        }
    }
}

/// A finite colouring instance: `1..=points`, `1..=colours`, forbidden sets.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ColouringProblem {
    points: usize,
    colours: usize,
    forbidden: Vec<Vec<usize>>,
}

impl ColouringProblem {
    /// Builds an instance from explicit forbidden sets.
    ///
    /// The sets are kept in the caller's order, because the encoding is order
    /// sensitive by design.
    ///
    /// # Errors
    ///
    /// [`ColouringError::InvalidParameter`] when `points` or `colours` is zero
    /// or a set is empty or not strictly ascending;
    /// [`ColouringError::PointOutOfRange`] when a set names a point outside
    /// `1..=points`.
    pub fn new(
        points: usize,
        colours: usize,
        forbidden: Vec<Vec<usize>>,
    ) -> Result<Self, ColouringError> {
        if points == 0 {
            return Err(ColouringError::InvalidParameter {
                what: "a colouring instance needs at least one point".to_string(),
            });
        }
        if colours == 0 {
            return Err(ColouringError::InvalidParameter {
                what: "a colouring instance needs at least one colour".to_string(),
            });
        }
        for set in &forbidden {
            if set.is_empty() {
                return Err(ColouringError::InvalidParameter {
                    what: "a forbidden set must name at least one point".to_string(),
                });
            }
            if set.windows(2).any(|pair| pair[0] >= pair[1]) {
                return Err(ColouringError::InvalidParameter {
                    what: format!("forbidden set {set:?} is not strictly ascending"),
                });
            }
            for &point in set {
                if point == 0 || point > points {
                    return Err(ColouringError::PointOutOfRange { point, points });
                }
            }
        }
        Ok(Self {
            points,
            colours,
            forbidden,
        })
    }

    /// Builds the instance a family induces on `1..=points`.
    ///
    /// # Errors
    ///
    /// As [`ColouringProblem::new`]; a family that emits an out-of-range or
    /// unsorted set is a bug in the family and is rejected here rather than
    /// encoded.
    pub fn from_family(
        family: &dyn SolutionFamily,
        points: usize,
        colours: usize,
    ) -> Result<Self, ColouringError> {
        Self::new(points, colours, family.solution_sets(points))
    }

    /// Number of points, the `n` of the instance.
    pub fn points(&self) -> usize {
        self.points
    }

    /// Number of colours, the `k` of the instance.
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
    /// [`ColouringError::PointOutOfRange`] or
    /// [`ColouringError::ColourOutOfRange`] for out-of-range arguments;
    /// [`ColouringError::Cnf`] when the index does not fit a [`CnfVar`].
    pub fn variable(&self, point: usize, colour: usize) -> Result<CnfVar, ColouringError> {
        if point == 0 || point > self.points {
            return Err(ColouringError::PointOutOfRange {
                point,
                points: self.points,
            });
        }
        if colour == 0 || colour > self.colours {
            return Err(ColouringError::ColourOutOfRange {
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
    pub fn literal(&self, point: usize, colour: usize) -> Result<CnfLit, ColouringError> {
        Ok(CnfLit::positive(self.variable(point, colour)?))
    }

    /// The at-least-one clause `{v(point,1) … v(point,colours)}`.
    ///
    /// # Errors
    ///
    /// As [`ColouringProblem::variable`].
    pub fn at_least_one(&self, point: usize) -> Result<Vec<CnfLit>, ColouringError> {
        (1..=self.colours).map(|i| self.literal(point, i)).collect()
    }

    /// Encodes with the generator-of-record profile
    /// ([`EncodingOptions::default`]).
    ///
    /// # Errors
    ///
    /// As [`ColouringProblem::encode_with`].
    pub fn encode(&self) -> Result<CnfFormula, ColouringError> {
        self.encode_with(EncodingOptions::default())
    }

    /// Encodes the instance to CNF.
    ///
    /// See the [module docs](self#clause-groups-in-emission-order) for the
    /// clause groups and their fixed order.
    ///
    /// # Errors
    ///
    /// [`ColouringError::Cnf`] if a variable index overflows `u32`.
    pub fn encode_with(&self, options: EncodingOptions) -> Result<CnfFormula, ColouringError> {
        let mut formula = CnfFormula::new(self.variable_count());
        for point in 1..=self.points {
            formula.add_clause(CnfClause::new(self.at_least_one(point)?))?;
        }
        for set in &self.forbidden {
            for colour in 1..=self.colours {
                let mut lits = Vec::with_capacity(set.len());
                for &point in set {
                    lits.push(self.literal(point, colour)?.negated());
                }
                formula.add_clause(CnfClause::new(lits))?;
            }
        }
        if options.at_most_one {
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
        }
        if options.symmetry_breaking {
            self.encode_symmetry_breaking(&mut formula)?;
        }
        Ok(formula)
    }

    /// Group 4: colour classes ordered by least element.
    fn encode_symmetry_breaking(&self, formula: &mut CnfFormula) -> Result<(), ColouringError> {
        formula.add_clause(CnfClause::new(vec![self.literal(1, 1)?]))?;
        for point in 2..=self.points {
            for colour in 2..=self.colours {
                // `point <= colour - 1`: no earlier point can already carry
                // colour `colour - 1`, so the clause degenerates to the unit
                // `-v(point, colour)`.
                //
                // This group is `O(n² k)` literals and dominates the formula at
                // ledger scale, so the clause is sized up front.
                let mut lits = Vec::with_capacity(point);
                lits.push(self.literal(point, colour)?.negated());
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

    /// Encodes and renders DIMACS with the generator-of-record profile.
    ///
    /// # Errors
    ///
    /// As [`ColouringProblem::encode`].
    pub fn to_dimacs(&self) -> Result<String, ColouringError> {
        Ok(self.encode()?.to_dimacs())
    }

    /// Decodes a CNF model into a colouring, one entry per point.
    ///
    /// # Errors
    ///
    /// [`ColouringError::ColouringLength`] if the model is shorter than
    /// [`ColouringProblem::variable_count`];
    /// [`ColouringError::ModelNotOneHot`] if some point does not get exactly one
    /// colour.
    pub fn decode_model(&self, values: &[bool]) -> Result<Vec<usize>, ColouringError> {
        if values.len() < self.variable_count() {
            return Err(ColouringError::ColouringLength {
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
                return Err(ColouringError::ModelNotOneHot {
                    point,
                    colours: count,
                });
            }
            colouring.push(chosen);
        }
        Ok(colouring)
    }

    /// The first forbidden set this colouring makes monochromatic, if any.
    ///
    /// This consults the instance's own set list, so it re-checks the
    /// **encoder's** view. Use [`verify_colouring`] to check a colouring against
    /// the relation itself.
    pub fn first_monochromatic(&self, colouring: &[usize]) -> Option<(Vec<usize>, usize)> {
        self.forbidden.iter().find_map(|set| {
            let first = *colouring.get(set[0] - 1)?;
            set.iter()
                .all(|&point| colouring.get(point - 1) == Some(&first))
                .then(|| (set.clone(), first))
        })
    }
}

/// Checks a colouring against a family's own relation, not against an encoding.
///
/// `colouring[j - 1]` is the colour of point `j`, and the number of points is
/// the colouring's length.
///
/// # Errors
///
/// [`ColouringError::ColourOutOfRange`] for a colour outside `1..=colours`, and
/// [`ColouringError::Monochromatic`] when the colouring is not a witness.
pub fn verify_colouring(
    family: &dyn SolutionFamily,
    colouring: &[usize],
    colours: usize,
) -> Result<(), ColouringError> {
    for &colour in colouring {
        if colour == 0 || colour > colours {
            return Err(ColouringError::ColourOutOfRange { colour, colours });
        }
    }
    match family.first_violation(colouring) {
        None => Ok(()),
        Some((members, colour)) => Err(ColouringError::Monochromatic { members, colour }),
    }
}

/// Widens a point index for coefficient arithmetic.
///
/// Point indices come from `1..=points`, and `usize` never exceeds `u64` on any
/// supported target, so this is exact; the saturating fallback is unreachable
/// and exists only to keep the function total. Coefficient products accumulate
/// in `i128` so that a large coefficient cannot wrap a sum into a spurious
/// solution — a wrapped sum would silently forbid a set that is not a solution,
/// or miss one that is.
fn widen(value: usize) -> i128 {
    i128::try_from(value).unwrap_or(i128::MAX)
}

/// Greatest common divisor, iterative and total on `usize`.
fn gcd(mut a: usize, mut b: usize) -> usize {
    while b != 0 {
        let rest = a % b;
        a = b;
        b = rest;
    }
    a
}

/// The Rado family `a(x − y) = b z`.
///
/// `R_k(a(x−y)=bz)` is the least `n` such that every `k`-colouring of `[1..n]`
/// has a monochromatic solution, so the instance for `n` is satisfiable exactly
/// when `R_k > n` (Chang–De Loera–Wesley, arXiv:2210.03262).
///
/// This family's [`solution_sets`](SolutionFamily::solution_sets) order is the
/// contract shared with `scripts/gen-rado-instance.py`, the generator of record
/// for `artifacts/claims/rado/`. Do not reorder it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Rado {
    a: usize,
    b: usize,
}

impl Rado {
    /// Builds `a(x − y) = b z`.
    ///
    /// # Errors
    ///
    /// [`ColouringError::InvalidParameter`] if `a` or `b` is zero.
    pub fn new(a: usize, b: usize) -> Result<Self, ColouringError> {
        if a == 0 || b == 0 {
            return Err(ColouringError::InvalidParameter {
                what: format!("rado needs a,b >= 1, got a={a} b={b}"),
            });
        }
        Ok(Self { a, b })
    }

    /// The `a` coefficient.
    pub fn a(self) -> usize {
        self.a
    }

    /// The `b` coefficient.
    pub fn b(self) -> usize {
        self.b
    }
}

impl SolutionFamily for Rado {
    fn name(&self) -> &'static str {
        "rado"
    }

    fn label(&self) -> String {
        format!("{}(x-y)={}z", self.a, self.b)
    }

    /// Enumerated as `x − y = b′t`, `z = a′t` for `t = 1, 2, …` with
    /// `g = gcd(a,b)`, `a′ = a/g`, `b′ = b/g`, inner loop over `y` ascending.
    ///
    /// Since `gcd(a′,b′) = 1`, `a(x−y) = bz` forces `b′ | x−y`, so this
    /// parameterisation is exactly the positive solution set — no more, no
    /// fewer. `t` is bounded by `a′t ≤ n` (else `z` leaves range) and
    /// `b′t + 1 ≤ n` (else no `y` admits `x = y + b′t ≤ n`); both bounds are
    /// monotone in `t`, so the loop stops at the first failure.
    fn solution_sets(&self, points: usize) -> Vec<Vec<usize>> {
        let divisor = gcd(self.a, self.b);
        let (step_z, step_x) = (self.a / divisor, self.b / divisor);
        let mut sets = Vec::new();
        let mut t = 1usize;
        loop {
            let (Some(z), Some(dx)) = (step_z.checked_mul(t), step_x.checked_mul(t)) else {
                break;
            };
            if z > points || dx + 1 > points {
                break;
            }
            for y in 1..=(points - dx) {
                sets.push(member_set(&[y + dx, y, z]));
            }
            t += 1;
        }
        sets
    }

    /// Brute force straight off `a(x − y) = b z`, over ordered pairs `y < x`.
    fn first_violation(&self, colouring: &[usize]) -> Option<(Vec<usize>, usize)> {
        let points = colouring.len();
        for x in 1..=points {
            for y in 1..x {
                let numerator = self.a.checked_mul(x - y)?;
                if numerator % self.b != 0 {
                    continue;
                }
                let z = numerator / self.b;
                if z == 0 || z > points {
                    continue;
                }
                let colour = colouring[x - 1];
                if colouring[y - 1] == colour && colouring[z - 1] == colour {
                    return Some((member_set(&[x, y, z]), colour));
                }
            }
        }
        None
    }
}

/// The Schur family `x + y = z`.
///
/// `R_2 = 5` and `R_3 = 14`: `[1..4]` has a 2-colouring free of monochromatic
/// `x + y = z` and `[1..5]` has none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Schur;

impl SolutionFamily for Schur {
    fn name(&self) -> &'static str {
        "schur"
    }

    fn label(&self) -> String {
        "x+y=z".to_string()
    }

    /// Enumerated with `z` ascending and, for each `z`, `x` ascending to
    /// `z / 2`, taking `y = z − x`. The upper bound on `x` removes the mirror
    /// pair `(x, y)`/`(y, x)`, which is the same set.
    fn solution_sets(&self, points: usize) -> Vec<Vec<usize>> {
        let mut sets = Vec::new();
        for z in 2..=points {
            for x in 1..=(z / 2) {
                sets.push(member_set(&[x, z - x, z]));
            }
        }
        sets
    }

    /// Brute force straight off `x + y = z`, over `x ≤ y`.
    fn first_violation(&self, colouring: &[usize]) -> Option<(Vec<usize>, usize)> {
        let points = colouring.len();
        for x in 1..=points {
            for y in x..=points {
                let z = x + y;
                if z > points {
                    break;
                }
                let colour = colouring[x - 1];
                if colouring[y - 1] == colour && colouring[z - 1] == colour {
                    return Some((member_set(&[x, y, z]), colour));
                }
            }
        }
        None
    }
}

/// The van der Waerden family: arithmetic progressions of a fixed length.
///
/// `W(k, length)` is the least `n` such that every `k`-colouring of `[1..n]`
/// contains a monochromatic `length`-term arithmetic progression, so the
/// instance for `n` is satisfiable exactly when `W(k, length) > n`. Known
/// values: `W(2,3) = 9`, `W(3,3) = 27`, `W(2,4) = 35`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VanDerWaerden {
    length: usize,
}

impl VanDerWaerden {
    /// Builds the family of `length`-term progressions.
    ///
    /// # Errors
    ///
    /// [`ColouringError::InvalidParameter`] if `length < 2`; a progression of
    /// one term is every point, and the instance would be trivially
    /// unsatisfiable for reasons that have nothing to do with van der Waerden.
    pub fn new(length: usize) -> Result<Self, ColouringError> {
        if length < 2 {
            return Err(ColouringError::InvalidParameter {
                what: format!("van der Waerden needs length >= 2, got {length}"),
            });
        }
        Ok(Self { length })
    }

    /// Number of terms in a progression.
    pub fn length(self) -> usize {
        self.length
    }
}

impl SolutionFamily for VanDerWaerden {
    fn name(&self) -> &'static str {
        "vdw"
    }

    fn label(&self) -> String {
        format!("AP_{}", self.length)
    }

    /// Enumerated with the first term `start` ascending and, for each `start`,
    /// the common difference `step` ascending while the last term
    /// `start + (length − 1) · step` stays inside `1..=points`.
    ///
    /// Progressions have `length` distinct terms because `step ≥ 1`, so no set
    /// collapses.
    fn solution_sets(&self, points: usize) -> Vec<Vec<usize>> {
        let mut sets = Vec::new();
        let span = self.length - 1;
        for start in 1..=points {
            let mut step = 1usize;
            while start + span * step <= points {
                sets.push((0..self.length).map(|term| start + term * step).collect());
                step += 1;
            }
        }
        sets
    }

    /// Brute force over strictly ascending `length`-tuples, testing the
    /// constant-difference property directly.
    ///
    /// This derives progressions from the *definition* ("the gaps are equal")
    /// rather than from the `(start, step)` parameterisation the encoder uses,
    /// which is the whole point. It costs `C(points, length)` tuples, so it is
    /// a checking route for instance-sized `points`, not a search route.
    fn first_violation(&self, colouring: &[usize]) -> Option<(Vec<usize>, usize)> {
        let points = colouring.len();
        let mut tuple = Vec::with_capacity(self.length);
        ascending_tuples(points, self.length, &mut tuple, &mut |terms: &[usize]| {
            let gap = terms[1] - terms[0];
            if terms.windows(2).any(|pair| pair[1] - pair[0] != gap) {
                return None;
            }
            let colour = colouring[terms[0] - 1];
            terms
                .iter()
                .all(|&point| colouring[point - 1] == colour)
                .then(|| (terms.to_vec(), colour))
        })
    }
}

/// Visits strictly ascending `arity`-tuples over `1..=points` in lexicographic
/// order, stopping at the first `Some`.
fn ascending_tuples<T>(
    points: usize,
    arity: usize,
    tuple: &mut Vec<usize>,
    visit: &mut dyn FnMut(&[usize]) -> Option<T>,
) -> Option<T> {
    if tuple.len() == arity {
        return visit(tuple);
    }
    let start = tuple.last().map_or(1, |&last| last + 1);
    // Leave room for the remaining coordinates, which must all be larger.
    let remaining = arity - tuple.len() - 1;
    for value in start..=points.checked_sub(remaining)? {
        tuple.push(value);
        let found = ascending_tuples(points, arity, tuple, visit);
        tuple.pop();
        if found.is_some() {
            return found;
        }
    }
    None
}

/// A homogeneous linear equation `c₁x₁ + … + c_mx_m = 0` over `1..=n`.
///
/// This is the general Rado-style relation: `Schur` is `[1, 1, -1]`,
/// `a(x−y) = bz` is `[a, -a, -b]`, and `x + 2y = 3z` is `[1, 2, -3]`. Use it
/// when the relation has no dedicated family; a dedicated family exists when its
/// enumeration order is a published contract ([`Rado`]) or when a
/// closed-form enumeration is much cheaper.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinearEquation {
    coefficients: Vec<i64>,
}

impl LinearEquation {
    /// Builds `c₁x₁ + … + c_mx_m = 0` from its coefficients.
    ///
    /// # Errors
    ///
    /// [`ColouringError::InvalidParameter`] if there are fewer than two
    /// coefficients or the **last** coefficient is zero. The last coefficient is
    /// the one the enumeration solves for, so it must be invertible; a zero
    /// elsewhere is fine and simply makes that variable free.
    pub fn new(coefficients: Vec<i64>) -> Result<Self, ColouringError> {
        if coefficients.len() < 2 {
            return Err(ColouringError::InvalidParameter {
                what: "a linear equation needs at least two coefficients".to_string(),
            });
        }
        if coefficients.last().copied().unwrap_or_default() == 0 {
            return Err(ColouringError::InvalidParameter {
                what: "the last coefficient is solved for and must be non-zero".to_string(),
            });
        }
        Ok(Self { coefficients })
    }

    /// The coefficients, in variable order.
    pub fn coefficients(&self) -> &[i64] {
        &self.coefficients
    }

    /// Number of variables.
    pub fn arity(&self) -> usize {
        self.coefficients.len()
    }
}

impl SolutionFamily for LinearEquation {
    fn name(&self) -> &'static str {
        "linear"
    }

    fn label(&self) -> String {
        let mut out = String::new();
        for (index, &coefficient) in self.coefficients.iter().enumerate() {
            if index > 0 {
                out.push_str(if coefficient < 0 { "-" } else { "+" });
            } else if coefficient < 0 {
                out.push('-');
            }
            let magnitude = coefficient.unsigned_abs();
            if magnitude != 1 {
                out.push_str(&magnitude.to_string());
            }
            out.push('x');
            out.push_str(&(index + 1).to_string());
        }
        out.push_str("=0");
        out
    }

    /// Enumerated by running `x₁ … x_{m−1}` lexicographically ascending over
    /// `1..=points` and solving the last coordinate,
    /// `x_m = −(c₁x₁ + … + c_{m−1}x_{m−1}) / c_m`, keeping it when it is an
    /// integer in range.
    ///
    /// Every solution appears exactly once, since the first `m − 1` coordinates
    /// determine the last. Note this order is **not** [`Rado`]'s: the two
    /// families agree as multisets of sets, not as sequences.
    fn solution_sets(&self, points: usize) -> Vec<Vec<usize>> {
        let arity = self.coefficients.len();
        let last = self.coefficients[arity - 1];
        let mut sets = Vec::new();
        let mut tuple = vec![1usize; arity];
        if points == 0 {
            return sets;
        }
        let last = i128::from(last);
        loop {
            let head: i128 = self.coefficients[..arity - 1]
                .iter()
                .zip(&tuple)
                .map(|(&coefficient, &value)| i128::from(coefficient) * widen(value))
                .sum();
            if head % last == 0
                && let Ok(solved) = usize::try_from(-head / last)
                && (1..=points).contains(&solved)
            {
                tuple[arity - 1] = solved;
                sets.push(member_set(&tuple));
            }
            // Odometer over the first `arity - 1` coordinates, last coordinate
            // fastest, so the enumeration is lexicographic in `x₁ … x_{m−1}`.
            let mut position = arity - 1;
            loop {
                if position == 0 {
                    return sets;
                }
                position -= 1;
                if tuple[position] < points {
                    tuple[position] += 1;
                    break;
                }
                tuple[position] = 1;
            }
        }
    }

    /// Brute force over **all** `m`-tuples in `1..=n`, evaluating
    /// `Σ cᵢxᵢ = 0` directly with no coordinate solved for.
    ///
    /// Costs `nᵐ` and is a checking route, not a search route.
    fn first_violation(&self, colouring: &[usize]) -> Option<(Vec<usize>, usize)> {
        let points = colouring.len();
        if points == 0 {
            return None;
        }
        let arity = self.coefficients.len();
        let mut tuple = vec![1usize; arity];
        loop {
            let total: i128 = self
                .coefficients
                .iter()
                .zip(&tuple)
                .map(|(&coefficient, &value)| i128::from(coefficient) * widen(value))
                .sum();
            if total == 0 {
                let colour = colouring[tuple[0] - 1];
                if tuple.iter().all(|&point| colouring[point - 1] == colour) {
                    return Some((member_set(&tuple), colour));
                }
            }
            let mut position = arity;
            loop {
                if position == 0 {
                    return None;
                }
                position -= 1;
                if tuple[position] < points {
                    tuple[position] += 1;
                    break;
                }
                tuple[position] = 1;
            }
        }
    }
}

/// Any relation at all, as a predicate over `arity`-tuples of `1..=n`.
///
/// This is the escape hatch the module promises: *forbid monochromatic tuples
/// satisfying a predicate*. It enumerates the full `nᵃʳⁱᵗʸ` product in
/// lexicographic order and keeps the tuples the predicate accepts, so it costs
/// `nᵃʳⁱᵗʸ` and is meant for small instances and for cross-checking a
/// closed-form family against its own definition — not for production
/// enumeration at ledger scale.
///
/// # Example
///
/// ```
/// use axeyum_cnf::colouring::{SolutionFamily, TuplePredicate};
///
/// // x + y = z, spelled as a predicate.
/// let family = TuplePredicate::new("schur-pred", "x+y=z", 3, |t: &[usize]| t[0] + t[1] == t[2])?;
/// // (1,1,2) (1,2,3) (2,1,3) (1,3,4) (2,2,4) (3,1,4): the mirror pairs are
/// // separate tuples, and each contributes its own (identical) member set.
/// assert_eq!(family.solution_sets(4).len(), 6);
/// # Ok::<(), axeyum_cnf::colouring::ColouringError>(())
/// ```
pub struct TuplePredicate<F> {
    name: &'static str,
    label: String,
    arity: usize,
    predicate: F,
}

impl<F> core::fmt::Debug for TuplePredicate<F> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("TuplePredicate")
            .field("name", &self.name)
            .field("label", &self.label)
            .field("arity", &self.arity)
            .finish_non_exhaustive()
    }
}

impl<F: Fn(&[usize]) -> bool> TuplePredicate<F> {
    /// Builds a family from a tuple predicate.
    ///
    /// # Errors
    ///
    /// [`ColouringError::InvalidParameter`] if `arity` is zero.
    pub fn new(
        name: &'static str,
        label: impl Into<String>,
        arity: usize,
        predicate: F,
    ) -> Result<Self, ColouringError> {
        if arity == 0 {
            return Err(ColouringError::InvalidParameter {
                what: "a tuple predicate needs arity >= 1".to_string(),
            });
        }
        Ok(Self {
            name,
            label: label.into(),
            arity,
            predicate,
        })
    }

    /// Visits every accepted tuple in lexicographic order.
    fn for_each_solution(&self, points: usize, visit: &mut dyn FnMut(&[usize]) -> bool) {
        if points == 0 {
            return;
        }
        let mut tuple = vec![1usize; self.arity];
        loop {
            if (self.predicate)(&tuple) && !visit(&tuple) {
                return;
            }
            let mut position = self.arity;
            loop {
                if position == 0 {
                    return;
                }
                position -= 1;
                if tuple[position] < points {
                    tuple[position] += 1;
                    break;
                }
                tuple[position] = 1;
            }
        }
    }
}

impl<F: Fn(&[usize]) -> bool> SolutionFamily for TuplePredicate<F> {
    fn name(&self) -> &'static str {
        self.name
    }

    fn label(&self) -> String {
        self.label.clone()
    }

    /// Every accepted tuple, in lexicographic order, as a sorted member set.
    ///
    /// Distinct tuples with the same member set (e.g. `(1,2,3)` and `(2,1,3)`
    /// for a symmetric predicate) each contribute a set, so the encoder emits
    /// the corresponding clause more than once. That is harmless — a repeated
    /// clause is a repeated constraint — but it is why symmetric relations get
    /// dedicated families with a canonical enumeration.
    fn solution_sets(&self, points: usize) -> Vec<Vec<usize>> {
        let mut sets = Vec::new();
        self.for_each_solution(points, &mut |tuple| {
            sets.push(member_set(tuple));
            true
        });
        sets
    }

    fn first_violation(&self, colouring: &[usize]) -> Option<(Vec<usize>, usize)> {
        let mut found = None;
        self.for_each_solution(colouring.len(), &mut |tuple| {
            let colour = colouring[tuple[0] - 1];
            if tuple.iter().all(|&point| colouring[point - 1] == colour) {
                found = Some((member_set(tuple), colour));
                return false;
            }
            true
        });
        found
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Solution sets compared as an order-insensitive multiset.
    fn as_multiset(mut sets: Vec<Vec<usize>>) -> Vec<Vec<usize>> {
        sets.sort_unstable();
        sets
    }

    #[test]
    fn variable_convention_is_one_based_row_major() {
        let problem = ColouringProblem::new(3, 2, vec![vec![1, 2, 3]]).expect("instance");
        assert_eq!(problem.variable(1, 1).expect("v(1,1)").dimacs(), 1);
        assert_eq!(problem.variable(1, 2).expect("v(1,2)").dimacs(), 2);
        assert_eq!(problem.variable(2, 1).expect("v(2,1)").dimacs(), 3);
        assert_eq!(problem.variable(3, 2).expect("v(3,2)").dimacs(), 6);
    }

    #[test]
    fn at_least_one_clauses_come_first_and_verbatim() {
        let problem = ColouringProblem::new(3, 2, vec![vec![1, 2, 3]]).expect("instance");
        let formula = problem.encode().expect("encode");
        for point in 1..=3 {
            assert_eq!(
                formula.clauses()[point - 1].lits(),
                problem.at_least_one(point).expect("alo")
            );
        }
    }

    #[test]
    fn clause_group_counts_match_the_documented_order() {
        let family = Rado::new(3, 2).expect("family");
        let problem = ColouringProblem::from_family(&family, 12, 3).expect("instance");
        let formula = problem.encode().expect("encode");
        let sets = problem.forbidden().len();
        let expected = 12 + sets * 3 + 12 * 3 + 1 + 11 * 2;
        assert_eq!(formula.clauses().len(), expected);
    }

    #[test]
    fn optional_groups_can_be_dropped() {
        let problem = ColouringProblem::new(4, 2, vec![vec![1, 2]]).expect("instance");
        let lean = problem
            .encode_with(EncodingOptions {
                at_most_one: false,
                symmetry_breaking: false,
            })
            .expect("encode");
        assert_eq!(lean.clauses().len(), 4 + 2);
    }

    #[test]
    fn out_of_range_and_unsorted_sets_are_rejected() {
        assert_eq!(
            ColouringProblem::new(3, 2, vec![vec![1, 4]]).expect_err("point 4 of 3"),
            ColouringError::PointOutOfRange {
                point: 4,
                points: 3
            }
        );
        assert!(matches!(
            ColouringProblem::new(3, 2, vec![vec![3, 1]]).expect_err("descending"),
            ColouringError::InvalidParameter { .. }
        ));
    }

    #[test]
    fn decode_model_rejects_a_point_with_two_colours() {
        let problem = ColouringProblem::new(3, 2, vec![vec![1, 2, 3]]).expect("instance");
        let mut values = vec![false; problem.variable_count()];
        values[0] = true;
        values[1] = true;
        values[2] = true;
        values[4] = true;
        assert_eq!(
            problem
                .decode_model(&values)
                .expect_err("point 1 is two-hot"),
            ColouringError::ModelNotOneHot {
                point: 1,
                colours: 2
            }
        );
    }

    #[test]
    fn rado_enumeration_matches_the_generator_parameterisation() {
        // a=3, b=2, n=8: g=1, so z = 3t and x - y = 2t.
        let sets = Rado::new(3, 2).expect("family").solution_sets(8);
        assert_eq!(sets[0], vec![1, 3]);
        assert_eq!(sets[1], vec![2, 3, 4]);
        assert_eq!(sets[2], vec![3, 5]);
        assert_eq!(sets[6], vec![1, 5, 6]);
    }

    #[test]
    fn rado_agrees_with_the_general_linear_equation_as_a_multiset() {
        for (a, b) in [(1, 1), (2, 3), (4, 3), (3, 2), (5, 4), (4, 2), (6, 4)] {
            let rado = Rado::new(a, b).expect("rado");
            let (wide_a, wide_b) = (
                i64::try_from(a).expect("small"),
                i64::try_from(b).expect("small"),
            );
            let linear =
                LinearEquation::new(vec![wide_a, -wide_a, -wide_b]).expect("linear equation");
            for points in [1usize, 2, 7, 20, 41] {
                assert_eq!(
                    as_multiset(rado.solution_sets(points)),
                    as_multiset(linear.solution_sets(points)),
                    "a={a} b={b} n={points}"
                );
            }
        }
    }

    /// Solution sets as an order- *and* multiplicity-insensitive set.
    ///
    /// A symmetric relation spelled with coefficients accepts both `(x,y,z)`
    /// and `(y,x,z)`, so [`LinearEquation`] and [`TuplePredicate`] emit mirror
    /// pairs twice where a dedicated family emits each set once. Repeating a
    /// clause repeats a constraint and changes nothing semantically, so the
    /// families are compared as sets when one of them is symmetric.
    fn as_set(sets: Vec<Vec<usize>>) -> Vec<Vec<usize>> {
        let mut sets = as_multiset(sets);
        sets.dedup();
        sets
    }

    #[test]
    fn schur_agrees_with_the_general_linear_equation() {
        let linear = LinearEquation::new(vec![1, 1, -1]).expect("linear equation");
        for points in [1usize, 2, 5, 14, 30] {
            assert_eq!(
                as_set(Schur.solution_sets(points)),
                as_set(linear.solution_sets(points)),
                "n={points}"
            );
        }
    }

    #[test]
    fn schur_agrees_with_the_raw_tuple_predicate() {
        let predicate =
            TuplePredicate::new("schur-pred", "x+y=z", 3, |t: &[usize]| t[0] + t[1] == t[2])
                .expect("predicate");
        for points in [1usize, 4, 9, 20] {
            assert_eq!(
                as_set(predicate.solution_sets(points)),
                as_set(Schur.solution_sets(points)),
                "n={points}"
            );
        }
    }

    #[test]
    fn van_der_waerden_enumerates_progressions_and_nothing_else() {
        let family = VanDerWaerden::new(3).expect("family");
        assert_eq!(family.solution_sets(5)[0], vec![1, 2, 3]);
        assert_eq!(family.solution_sets(5)[1], vec![1, 3, 5]);
        let predicate = TuplePredicate::new("ap3", "AP_3", 3, |t: &[usize]| {
            t[0] < t[1] && t[1] < t[2] && t[1] - t[0] == t[2] - t[1]
        })
        .expect("predicate");
        for points in [3usize, 9, 20] {
            assert_eq!(
                as_multiset(family.solution_sets(points)),
                as_multiset(predicate.solution_sets(points)),
                "n={points}"
            );
        }
    }

    #[test]
    fn van_der_waerden_witness_check_is_independent_of_the_encoding() {
        let family = VanDerWaerden::new(3).expect("family");
        // W(2,3) = 9: this 2-colouring of [1..8] has no monochromatic 3-AP.
        let good = [1, 1, 2, 2, 1, 1, 2, 2];
        verify_colouring(&family, &good, 2).expect("no monochromatic 3-AP in [1..8]");
        // 1,2,3 all colour 1.
        assert_eq!(
            verify_colouring(&family, &[1, 1, 1, 2], 2).expect_err("1,2,3 is a mono AP"),
            ColouringError::Monochromatic {
                members: vec![1, 2, 3],
                colour: 1
            }
        );
    }

    #[test]
    fn brute_force_and_encoder_views_agree_on_pseudorandom_colourings() {
        let rado = Rado::new(4, 3).expect("rado");
        let vdw = VanDerWaerden::new(3).expect("vdw");
        let families: [(&dyn SolutionFamily, usize); 3] = [(&rado, 24), (&Schur, 24), (&vdw, 24)];
        let mut compared = 0usize;
        for (family, points) in families {
            let problem = ColouringProblem::from_family(family, points, 3).expect("instance");
            let mut state = 0x2026_0812_u64;
            for _ in 0..64 {
                let colouring: Vec<usize> = (0..points)
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
                    "{}: independent and encoder views disagree on {colouring:?}",
                    family.name()
                );
                compared += 1;
            }
        }
        assert_eq!(compared, 192);
    }

    #[test]
    fn verify_colouring_rejects_a_lying_search() {
        assert_eq!(
            verify_colouring(&Schur, &[1, 1, 1], 2).expect_err("1+1=2 is monochromatic"),
            ColouringError::Monochromatic {
                members: vec![1, 2],
                colour: 1
            }
        );
        assert_eq!(
            verify_colouring(&Schur, &[1, 3], 2).expect_err("colour 3 of 2"),
            ColouringError::ColourOutOfRange {
                colour: 3,
                colours: 2
            }
        );
    }

    #[test]
    fn linear_equation_rejects_a_zero_final_coefficient() {
        assert!(matches!(
            LinearEquation::new(vec![1, 1, 0]).expect_err("last coefficient is solved for"),
            ColouringError::InvalidParameter { .. }
        ));
        assert!(matches!(
            LinearEquation::new(vec![1]).expect_err("needs two coefficients"),
            ColouringError::InvalidParameter { .. }
        ));
    }

    #[test]
    fn labels_are_stable_and_readable() {
        assert_eq!(Rado::new(4, 3).expect("rado").label(), "4(x-y)=3z");
        assert_eq!(Schur.label(), "x+y=z");
        assert_eq!(VanDerWaerden::new(4).expect("vdw").label(), "AP_4");
        assert_eq!(
            LinearEquation::new(vec![1, 2, -3])
                .expect("linear equation")
                .label(),
            "x1+2x2-3x3=0"
        );
    }

    #[test]
    fn degenerate_instances_encode_without_panicking() {
        for family in [
            Rado::new(1, 1).expect("rado"),
            Rado::new(9, 7).expect("rado"),
        ] {
            for points in 1usize..=3 {
                let problem = ColouringProblem::from_family(&family, points, 1).expect("instance");
                let formula = problem.encode().expect("encode");
                assert_eq!(formula.variable_count(), points);
            }
        }
    }
}
