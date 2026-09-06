//! The **lifting phase**: a cell of the `x`-line becomes a cell of the
//! `(x, y)`-plane with a sample point, and is projected once more, so
//! `∃z. ⋀ᵢ pᵢ(x, y, z) ▷ᵢ 0` is decided at a bounded total degree.
//!
//! This is the step [`crate::qe::bivariate`] named as missing: there is now a
//! cell-to-plane phase, so the module is a (bounded, three-variable)
//! cylindrical algebraic decomposition rather than a single projection.
//!
//! # The three levels
//!
//! Write `A` for the atom polynomials `pᵢ(x, y, z)`.
//!
//! 1. **Project `z` out.** `P₁ = PROJ_z(A)` — the leading coefficient of every
//!    reductum of every `pᵢ` in `z`, the discriminant `res_z(r, ∂r/∂z)` of
//!    every reductum of `z`-degree at least two, the resultant `res_z(r, s)` of
//!    every pair of distinct reducta, and the `z`-free part of every `pᵢ`. Each
//!    is a polynomial in `(x, y)`. The Sylvester determinant is taken over the
//!    **ring `ℚ[x, y]`** (`ring_determinant`, a Laplace expansion over column
//!    subsets), in [`num_rational::BigRational`] — no `i128` and no `f64`.
//! 2. **Project `y` out of `P₁`.** `P₂ = PROJ_y(P₁)`, polynomials in `x` alone.
//!    This is *exactly* [`crate::qe::bivariate`]'s projection operator, reused
//!    verbatim through `bivariate::projection_set_of_polys`, so the two levels
//!    cannot drift apart. `P₁` is handed to it on the `i128` surface; a
//!    coefficient that does not fit is a named decline, never a guess.
//! 3. **Decompose, then lift.** The real roots of `P₂` cut the `x`-line into
//!    `2r + 1` cells. Over each cell's sample `x₀` the polynomials of `P₁`
//!    become univariate in `y`; their real roots cut the `y`-line into
//!    `2s + 1` cells, and *that* is the lifting — the cell `C × (y-cell)` is a
//!    cell of the plane, carrying the sample `(x₀, y₀)`. Over each such sample
//!    the atoms are univariate in `z` and the fibre is decided exactly.
//!
//! # The delineability hypothesis, and what the degree bound guarantees
//!
//! The soundness of one sample per cell is Collins' projection theorem
//! (G. E. Collins, *Quantifier elimination for real closed fields by
//! cylindrical algebraic decomposition*, Automata Theory and Formal Languages
//! (2nd GI Conference), Lecture Notes in Computer Science 33, Springer 1975,
//! pp. 134–183; the delineability theorem is Theorem 4 there, and the same
//! statement is Theorem 5.6 of Caviness & Johnson, *Quantifier Elimination and
//! Cylindrical Algebraic Decomposition*, Springer 1998).
//!
//! Applied twice, it says:
//!
//! - **Level 2 → level 1.** On a cell `C` of the `x`-line where no polynomial
//!   of `P₂` vanishes (unless identically), every element of `P₁` is
//!   *delineable* over `C`: its `y`-degree does not drop, its roots do not
//!   collide with each other, and no root of one meets a root of another. So
//!   the real roots of `P₁` over `C` are continuous, non-crossing branches, and
//!   the `y`-cells found over the single sample `x₀` are the cells of the whole
//!   cylinder above `C`.
//! - **Level 1 → level 0.** On such a plane cell `D`, no polynomial of `P₁`
//!   vanishes, so every `pᵢ` is delineable over `D` in `z`: the sign vector of
//!   `(p₁, …, pₙ)` along the `z`-line is the same at every point of `D`. The
//!   truth of `∃z. ⋀ᵢ pᵢ ▷ᵢ 0` is a function of that sign vector alone, hence
//!   **constant on `D`**, and the one sample decides the whole cell.
//!
//! Point cells need no delineability argument: a point cell *is* one sample.
//!
//! The bound `total degree ≤ `[`MAX_TOTAL_DEGREE`]` = 3` is what keeps the
//! exhaustive Collins set finite and small. It bounds `deg_z pᵢ ≤ 3`, so an
//! atom has at most four reducta and every Sylvester matrix at level 1 is at
//! most `6 × 6`; the level-2 call then inherits
//! [`crate::qe::bivariate::MAX_TOTAL_DEGREE`]'s machinery without inheriting
//! its bound, because a projection polynomial is not an atom — a level-1
//! discriminant already has total degree up to 15. A degree-4 **input** is
//! refused by name ([`Fault::DegreeBoundExceeded`]) rather than attempted.
//!
//! # What is decided, and what declines
//!
//! **Decided.** `∃z. ⋀ᵢ pᵢ(x, y, z) ▷ᵢ 0` at total degree at most three, over
//! every cell of the `x`-line whose sample is **rational** — which is every
//! cell when the level-2 cut points are rational — including the plane cells
//! whose `y`-sample is a real algebraic number, which go through
//! [`crate::qe::fibre`]'s `ℚ(β)` engine exactly as the bivariate step's
//! irrational boundaries do.
//!
//! **Declined, by name.**
//!
//! - An **algebraic `x`-cut point**. Its cell is marked
//!   [`YLine::TowerDepthUnsupported`] and every other cell is still decided;
//!   the certificate is then not total, which [`LiftCertificate::is_total`]
//!   reports. Deciding it needs the `y`-line over `K = ℚ(α)` and then a fibre
//!   over `K(β)` — a **tower of depth two**, which [`crate::qe::fibre`] does
//!   not build: its `RealField` is `ℚ[x]/(m)` over ℚ, not over another field.
//! - A **repeated `z`-factor** ([`Fault::DegenerateProjection`]). The bivariate
//!   step's pseudo-division fallback is not carried over to `ℚ[x, y]`
//!   coefficients here.
//! - Two atoms sharing a factor of positive `z`-degree, likewise degenerate.
//! - A level-1 coefficient too large for the `i128` surface the level-2
//!   projection is written against ([`Fault::Declined`]).
//!
//! # Cost — ADVISORY
//!
//! Measured 2026-09-05 on this box, `--release`, three repeats of a prebuilt
//! lib-test binary, load stated in the table. **Advisory only**; do not ratchet
//! on these. Every row is producer **plus** a full independent `verify`.
//!
//! | shape | cells | cost |
//! |---|---|---|
//! | degree 2, `∃z. x² + y² + z² < 1` (the open disc) | 5 `x`-cells, 17 plane cells | see the item-7 log row |
//! | degree 2, `∃z. z² = x ∧ z² = y` | 3 `x`-cells, 13 plane cells | see the item-7 log row |
//! | degree 2, `∃z. x·z = 1 ∧ y·z = 1` | 3 `x`-cells, 13 plane cells | see the item-7 log row |
//!
//! The dominant term is the same one the bivariate step measured: a plane cell
//! whose `y`-sample is algebraic costs roughly sixty times a rational one,
//! because every sign in its Sturm chain is a sign at `β` rather than a sign of
//! a rational.
//!
//! # What this module reuses
//!
//! - `bivariate::projection_set_of_polys`, `projection_cut`, `isolate_cut`,
//!   `cut_points`, `check_sample_in_cell`, `divides`, `bipoly_of_big` — the
//!   whole level-2 projection and the `x`-line decomposition;
//! - [`crate::qe::decompose`] — the `y`-line decomposition over ℚ;
//! - [`crate::qe::decide_exists`] — the `z`-fibre at a rational `(x₀, y₀)`;
//! - [`crate::qe::fibre::decide_fibre`] — the `z`-fibre over an algebraic `β`,
//!   with `β` playing the role that `α` plays for the bivariate step.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use super::bivariate::{self, BigBiPoly};
use super::{
    Atom, Decision, ExistsFormula, Relation, SamplePoint, big, decompose, decide_exists, fibre,
    open_cell_samples,
};

/// The largest total degree this step accepts in any atom.
pub const MAX_TOTAL_DEGREE: usize = 3;

/// A trivariate polynomial: `poly[k]` is the coefficient of `zᵏ`, itself a
/// polynomial in `(x, y)` whose `[j]` entry is the LSB-first ℚ-polynomial in
/// `x` multiplying `yʲ`.
pub type TriPoly = Vec<BigBiPoly>;

/// One trivariate atom `poly(x, y, z) ▷ 0`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TriAtom {
    /// The polynomial.
    pub poly: TriPoly,
    /// The comparison against `0`.
    pub relation: Relation,
}

impl TriAtom {
    /// Build a trivariate atom.
    #[must_use]
    pub fn new(poly: TriPoly, relation: Relation) -> TriAtom {
        TriAtom { poly, relation }
    }
}

/// `∃z. ⋀ᵢ atoms[i]`, with `x` and `y` left free.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ExistsZFormula {
    /// The conjuncts. An **empty** conjunction is `true` everywhere.
    pub atoms: Vec<TriAtom>,
}

impl ExistsZFormula {
    /// Build `∃z. ⋀ atoms`.
    #[must_use]
    pub fn new(atoms: Vec<TriAtom>) -> ExistsZFormula {
        ExistsZFormula { atoms }
    }
}

/// A trivariate polynomial from monomials `(coefficient, x-power, y-power,
/// z-power)`. Terms may repeat; they are summed.
///
/// ```
/// use axeyum_cas::qe::lift::tri_terms;
///
/// // x·z − 1
/// let p = tri_terms(&[(1, 1, 0, 1), (-1, 0, 0, 0)]);
/// assert_eq!(p.len(), 2);
/// ```
#[must_use]
pub fn tri_terms(terms: &[(i64, usize, usize, usize)]) -> TriPoly {
    let mut out: TriPoly = Vec::new();
    for &(coefficient, x_power, y_power, z_power) in terms {
        if out.len() <= z_power {
            out.resize(z_power + 1, Vec::new());
        }
        let level = &mut out[z_power];
        if level.len() <= y_power {
            level.resize(y_power + 1, Vec::new());
        }
        let row = &mut level[y_power];
        if row.len() <= x_power {
            row.resize(x_power + 1, BigRational::zero());
        }
        row[x_power] += BigRational::from_integer(BigInt::from(coefficient));
    }
    out
}

// ============================================================================
// Faults.
// ============================================================================

/// Why a lifted decomposition, or its certificate, was refused. Every variant
/// is a **distinct guard**; [`Fault::Declined`] is the one that is not an
/// accusation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Fault {
    /// An atom exceeds [`MAX_TOTAL_DEGREE`].
    DegreeBoundExceeded {
        /// Index of the offending atom.
        atom: usize,
        /// Its total degree.
        total_degree: usize,
        /// The bound it exceeds.
        bound: usize,
    },
    /// A level-1 projection polynomial vanishes identically, so delineability
    /// in `z` does not apply.
    DegenerateProjection {
        /// What was being computed.
        what: &'static str,
    },
    /// The level-2 projection refused; the bivariate module's own fault says
    /// why.
    LevelTwoProjection(Box<bivariate::Fault>),
    /// The recomputed level-1 (`z`-elimination) set is not the recorded one.
    ProjectionZMismatch {
        /// Polynomials recorded.
        recorded: usize,
        /// Polynomials re-derived.
        recomputed: usize,
    },
    /// The recomputed level-2 (`y`-elimination) set is not the recorded one.
    ProjectionYMismatch {
        /// Polynomials recorded.
        recorded: usize,
        /// Polynomials re-derived.
        recomputed: usize,
    },
    /// The recomputed `x`-cut polynomial is not the recorded one.
    CutMismatch {
        /// The degree recorded.
        recorded: usize,
        /// The degree re-derived.
        recomputed: usize,
    },
    /// The recorded `x`-cut points are not the real roots of the level-2 set.
    RootsMismatch {
        /// Roots recorded.
        recorded: usize,
        /// Roots re-derived.
        recomputed: usize,
    },
    /// A recorded `x`-cut point is not the re-derived one at that position.
    RootValueMismatch {
        /// Which cut point.
        index: usize,
    },
    /// The certificate records the wrong number of `x`-cells (`2r + 1`).
    CellCountMismatch {
        /// Cells recorded.
        recorded: usize,
        /// Cells required.
        expected: usize,
    },
    /// An `x`-cell's recorded sample does not lie in that cell.
    CellSampleOutOfOrder {
        /// The offending `x`-cell.
        cell: usize,
    },
    /// An `x`-cell with a **rational** sample is marked as a tower decline,
    /// which would let a decidable cell hide behind an unsupported one.
    TowerDepthMisapplied {
        /// The offending `x`-cell.
        cell: usize,
    },
    /// The `y`-cut points recomputed over an `x`-cell's sample are not the
    /// recorded ones.
    YRootsMismatch {
        /// The offending `x`-cell.
        cell: usize,
        /// Roots recorded.
        recorded: usize,
        /// Roots re-derived.
        recomputed: usize,
    },
    /// A recorded `y`-cut point is not the re-derived one at that position.
    YRootValueMismatch {
        /// The offending `x`-cell.
        cell: usize,
        /// Which `y`-cut point.
        index: usize,
    },
    /// An `x`-cell records the wrong number of `y`-cells (`2s + 1`).
    YCellCountMismatch {
        /// The offending `x`-cell.
        cell: usize,
        /// `y`-cells recorded.
        recorded: usize,
        /// `y`-cells required.
        expected: usize,
    },
    /// A plane cell's recorded `y`-sample does not lie in that `y`-cell.
    YCellSampleOutOfOrder {
        /// The offending `x`-cell.
        cell: usize,
        /// The offending `y`-cell.
        y_cell: usize,
    },
    /// A plane cell's fibre certificate is of the wrong kind for its
    /// `y`-sample: a rational sample needs the ℚ route and an algebraic one
    /// the `ℚ(β)` route.
    FibreKindMismatch {
        /// The offending `x`-cell.
        cell: usize,
        /// The offending `y`-cell.
        y_cell: usize,
    },
    /// A plane cell's fibre certificate is not about the atoms obtained by
    /// substituting **this** cell's sample, so it decides another formula.
    SubstitutionMismatch {
        /// The offending `x`-cell.
        cell: usize,
        /// The offending `y`-cell.
        y_cell: usize,
    },
    /// An algebraic plane cell's fibre names a different bracket than the
    /// `y`-cut point it is supposed to be about, so it speaks about another
    /// `β`.
    FibreBracketMismatch {
        /// The offending `x`-cell.
        cell: usize,
        /// The offending `y`-cell.
        y_cell: usize,
    },
    /// An algebraic plane cell's fibre modulus does not divide the `y`-cut
    /// polynomial, so the `β` it presents need not be a branch point at all.
    ModulusNotADivisor {
        /// The offending `x`-cell.
        cell: usize,
        /// The offending `y`-cell.
        y_cell: usize,
    },
    /// A plane cell's recorded verdict is not the one its fibre establishes.
    CellVerdictMismatch {
        /// The offending `x`-cell.
        cell: usize,
        /// The offending `y`-cell.
        y_cell: usize,
        /// The verdict recorded.
        recorded: bool,
        /// The verdict the certificate establishes.
        recomputed: bool,
    },
    /// A plane cell's univariate (rational `(x₀, y₀)`) certificate was refused.
    Univariate {
        /// The offending `x`-cell.
        cell: usize,
        /// The offending `y`-cell.
        y_cell: usize,
        /// The univariate guard that rejected.
        fault: super::Fault,
    },
    /// A plane cell's `ℚ(β)` fibre certificate was refused.
    Fibre {
        /// The offending `x`-cell.
        cell: usize,
        /// The offending `y`-cell.
        y_cell: usize,
        /// The fibre guard that rejected.
        fault: fibre::Fault,
    },
    /// Exact arithmetic ran out of a named step budget, or a value did not fit
    /// the `i128` surface the level-2 projection is written against. Not a
    /// refusal of any claim.
    Declined(String),
}

// ============================================================================
// The certificate.
// ============================================================================

/// How one plane cell's `z`-fibre was decided.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ZFibre {
    /// Both samples are rational, so the fibre is an ordinary univariate
    /// problem over ℚ.
    Rational(Decision),
    /// The `y`-sample is a real algebraic `β`, so the fibre was decided in
    /// `ℚ(β)`.
    Algebraic(Box<fibre::FibreCertificate>),
}

/// One cell of the `(x, y)`-plane: its `y`-sample, the verdict there, and the
/// fibre certificate that establishes it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PlaneCell {
    /// The `y` at which the `z`-fibre was decided.
    pub sample: SamplePoint,
    /// Whether `∃z. ⋀ᵢ pᵢ(x₀, y₀, z) ▷ᵢ 0` holds.
    pub verdict: bool,
    /// The fibre decision in `z`, certificate and all.
    pub fibre: ZFibre,
}

/// The `y`-line over one `x`-cell: either the lifted cells, or the named
/// decline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum YLine {
    /// The lift succeeded: the `y`-cut points over the `x`-sample, and the
    /// `2s + 1` plane cells above it.
    Lifted {
        /// The distinct real roots of the level-1 set at the `x`-sample.
        roots: Vec<SamplePoint>,
        /// One entry per `y`-cell, interleaved as
        /// `(−∞, β₀)`, `{β₀}`, `(β₀, β₁)`, ….
        cells: Vec<PlaneCell>,
    },
    /// The `x`-sample is a real algebraic number, so the `y`-line would have to
    /// be decomposed over `K = ℚ(α)` and the fibre decided over a **tower**
    /// `K(β)`. [`crate::qe::fibre`] builds `ℚ(α)` over ℚ only, so this cell is
    /// declined by name and every other cell is still decided.
    TowerDepthUnsupported,
}

/// One cell of the `x`-line, together with the cylinder above it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct XCell {
    /// The `x` at which the cylinder was built — rational for an open cell,
    /// the cut point itself for a point cell.
    pub sample: SamplePoint,
    /// The `y`-line above it.
    pub line: YLine,
}

/// The result of eliminating `z`: the `(x, y)`-plane as a cylindrical cell
/// list with a verdict per cell, and everything needed to re-derive it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LiftCertificate {
    /// The formula this certificate is about.
    pub atoms: Vec<TriAtom>,
    /// The level-1 projection set `PROJ_z(A)`, canonical and ordered.
    pub projection_z: Vec<BigBiPoly>,
    /// The level-2 projection set `PROJ_y(PROJ_z(A))`, monic and ordered.
    pub projection_y: Vec<Vec<axeyum_ir::Rational>>,
    /// The `x`-cut polynomial: the square-free part of the level-2 set's
    /// product.
    pub cut: Vec<BigRational>,
    /// The `x`-cut points, ascending.
    pub roots: Vec<SamplePoint>,
    /// One entry per `x`-cell, interleaved `(−∞, α₀)`, `{α₀}`, `(α₀, α₁)`, ….
    pub cells: Vec<XCell>,
}

impl LiftCertificate {
    /// Whether every `x`-cell was decided — false when some cell is a
    /// [`YLine::TowerDepthUnsupported`] decline.
    #[must_use]
    pub fn is_total(&self) -> bool {
        self.cells
            .iter()
            .all(|cell| matches!(cell.line, YLine::Lifted { .. }))
    }

    /// Re-derive the whole decomposition from `atoms` alone.
    ///
    /// Guards, in order: the degree bound still holds; the level-1 set
    /// recomputed from the atoms is exactly the recorded one; so is the level-2
    /// set, the `x`-cut polynomial and the `x`-cut points; the `x`-cell count
    /// matches; every `x`-sample lies in its own cell, in order; a tower
    /// decline appears only at an algebraic sample; and then, over each
    /// `x`-cell, the `y`-cut points recomputed by substituting the sample into
    /// the level-1 set are exactly the recorded ones, every `y`-sample lies in
    /// its own `y`-cell in order, and every plane cell's fibre certificate is
    /// of the right kind, is about the atoms this checker itself substitutes,
    /// and establishes the recorded verdict.
    ///
    /// Nothing the producer computed is reused — not a projection polynomial,
    /// not a root, not a sign, and for an algebraic plane cell not the
    /// substituted `ℚ(β)` coefficients either.
    ///
    /// # Errors
    ///
    /// The [`Fault`] naming the guard that rejected.
    pub fn verify(&self) -> Result<(), Fault> {
        check_degree_bound(&self.atoms)?;
        self.check_projections()?;
        let roots = bivariate::cut_points(&self.cut).map_err(lift_bivariate_fault)?;
        self.check_roots(&roots)?;
        for (cell, entry) in self.cells.iter().enumerate() {
            bivariate::check_sample_in_cell(&roots, cell, &entry.sample)
                .map_err(|_| Fault::CellSampleOutOfOrder { cell })?;
            self.check_x_cell(cell, entry)?;
        }
        Ok(())
    }

    /// Both projection sets and the cut polynomial, re-derived from the atoms.
    fn check_projections(&self) -> Result<(), Fault> {
        let level_one = projection_z(&self.atoms)?;
        if level_one != self.projection_z {
            return Err(Fault::ProjectionZMismatch {
                recorded: self.projection_z.len(),
                recomputed: level_one.len(),
            });
        }
        let level_two = projection_y(&level_one)?;
        if level_two != self.projection_y {
            return Err(Fault::ProjectionYMismatch {
                recorded: self.projection_y.len(),
                recomputed: level_two.len(),
            });
        }
        let cut = bivariate::projection_cut(&level_two);
        if cut != self.cut {
            return Err(Fault::CutMismatch {
                recorded: big::degree(&self.cut).unwrap_or(0),
                recomputed: big::degree(&cut).unwrap_or(0),
            });
        }
        Ok(())
    }

    /// The recorded `x`-cut points and the `x`-cell count.
    fn check_roots(&self, roots: &[SamplePoint]) -> Result<(), Fault> {
        if roots.len() != self.roots.len() {
            return Err(Fault::RootsMismatch {
                recorded: self.roots.len(),
                recomputed: roots.len(),
            });
        }
        for (index, root) in roots.iter().enumerate() {
            if *root != self.roots[index] {
                return Err(Fault::RootValueMismatch { index });
            }
        }
        let expected = 2 * roots.len() + 1;
        if self.cells.len() != expected {
            return Err(Fault::CellCountMismatch {
                recorded: self.cells.len(),
                expected,
            });
        }
        Ok(())
    }

    /// One `x`-cell: the tower marker is honest, and the cylinder above it
    /// re-derives.
    fn check_x_cell(&self, cell: usize, entry: &XCell) -> Result<(), Fault> {
        let (roots, cells) = match (&entry.sample, &entry.line) {
            (SamplePoint::Algebraic { .. }, YLine::TowerDepthUnsupported) => return Ok(()),
            (SamplePoint::Rational(_), YLine::TowerDepthUnsupported) => {
                return Err(Fault::TowerDepthMisapplied { cell });
            }
            (_, YLine::Lifted { roots, cells }) => (roots, cells),
        };
        let SamplePoint::Rational(x) = &entry.sample else {
            return Err(Fault::TowerDepthMisapplied { cell });
        };
        let fibre_atoms = y_line_atoms(&self.projection_z, x);
        let decomposition =
            decompose(&fibre_atoms).map_err(|reason| Fault::Declined(format!("cell {cell}: {reason}")))?;
        let recomputed: Vec<SamplePoint> = decomposition
            .roots
            .iter()
            .map(|root| SamplePoint::from_isolated(&decomposition.cut, root))
            .collect();
        check_y_roots(cell, roots, &recomputed)?;
        if cells.len() != 2 * recomputed.len() + 1 {
            return Err(Fault::YCellCountMismatch {
                cell,
                recorded: cells.len(),
                expected: 2 * recomputed.len() + 1,
            });
        }
        for (y_cell, plane) in cells.iter().enumerate() {
            bivariate::check_sample_in_cell(&recomputed, y_cell, &plane.sample)
                .map_err(|_| Fault::YCellSampleOutOfOrder { cell, y_cell })?;
            let verdict = self.check_plane_cell(cell, y_cell, x, &decomposition.cut, plane)?;
            if verdict != plane.verdict {
                return Err(Fault::CellVerdictMismatch {
                    cell,
                    y_cell,
                    recorded: plane.verdict,
                    recomputed: verdict,
                });
            }
        }
        Ok(())
    }

    /// One plane cell's fibre: right kind, right formula, own verdict.
    fn check_plane_cell(
        &self,
        cell: usize,
        y_cell: usize,
        x: &BigRational,
        y_cut: &[BigRational],
        plane: &PlaneCell,
    ) -> Result<bool, Fault> {
        match (&plane.sample, &plane.fibre) {
            (SamplePoint::Rational(y), ZFibre::Rational(decision)) => {
                let substituted = substitute_xy(&self.atoms, x, y);
                if certificate_atoms(decision) != Some(substituted) {
                    return Err(Fault::SubstitutionMismatch { cell, y_cell });
                }
                decision
                    .verify()
                    .map_err(|fault| Fault::Univariate {
                        cell,
                        y_cell,
                        fault,
                    })?
                    .ok_or_else(|| {
                        Fault::Declined(format!("plane cell {cell}/{y_cell} carries no claim"))
                    })
            }
            (SamplePoint::Algebraic { lower, upper, .. }, ZFibre::Algebraic(certificate)) => self
                .check_algebraic_fibre(cell, y_cell, x, y_cut, lower, upper, certificate),
            _ => Err(Fault::FibreKindMismatch { cell, y_cell }),
        }
    }

    /// The `ℚ(β)` route's extra obligations: the modulus really presents *this*
    /// branch point, and the substituted atoms are the checker's own.
    #[allow(clippy::too_many_arguments)]
    fn check_algebraic_fibre(
        &self,
        cell: usize,
        y_cell: usize,
        x: &BigRational,
        y_cut: &[BigRational],
        lower: &BigRational,
        upper: &BigRational,
        certificate: &fibre::FibreCertificate,
    ) -> Result<bool, Fault> {
        if certificate.lower != *lower || certificate.upper != *upper {
            return Err(Fault::FibreBracketMismatch { cell, y_cell });
        }
        if !bivariate::divides(&certificate.modulus, y_cut) {
            return Err(Fault::ModulusNotADivisor { cell, y_cell });
        }
        let field = fibre::RealField::new(&certificate.modulus, lower, upper).map_err(|fault| {
            Fault::Fibre {
                cell,
                y_cell,
                fault,
            }
        })?;
        let substituted = fibre::substitute(&field, &substitute_x(&self.atoms, x));
        if certificate.atoms != substituted {
            return Err(Fault::SubstitutionMismatch { cell, y_cell });
        }
        certificate.verify().map_err(|fault| Fault::Fibre {
            cell,
            y_cell,
            fault,
        })
    }

    /// The true cells, as a human-readable union. Call
    /// [`LiftCertificate::verify`] first: this reads the recorded verdicts.
    ///
    /// Each piece names the `x`-cell and the `y`-cell of the cylinder above it;
    /// a `y`-cell is named by its **branch index**, because a branch of the
    /// level-1 set is a continuous function of `x` over the cell and has no
    /// closed form in general. The sample is printed so the branch is
    /// identifiable.
    #[must_use]
    pub fn describe(&self) -> String {
        let mut pieces: Vec<String> = Vec::new();
        for (cell, entry) in self.cells.iter().enumerate() {
            match &entry.line {
                YLine::TowerDepthUnsupported => {
                    pieces.push(format!("{}: undecided (tower)", self.x_cell_name(cell)));
                }
                YLine::Lifted { roots, cells } => {
                    for (y_cell, plane) in cells.iter().enumerate() {
                        if plane.verdict {
                            pieces.push(format!(
                                "{{{}, {}}}",
                                self.x_cell_name(cell),
                                y_cell_name(y_cell, roots.len(), &plane.sample)
                            ));
                        }
                    }
                }
            }
        }
        if pieces.is_empty() {
            return "∅".to_string();
        }
        pieces.join(" ∪ ")
    }

    /// The printed name of one `x`-cell.
    fn x_cell_name(&self, cell: usize) -> String {
        let last = self.roots.len();
        if cell.is_multiple_of(2) {
            let k = cell / 2;
            let left = if k == 0 {
                "-∞".to_string()
            } else {
                root_name(&self.roots, k - 1)
            };
            let right = if k == last {
                "∞".to_string()
            } else {
                root_name(&self.roots, k)
            };
            format!("x ∈ ({left}, {right})")
        } else {
            format!("x = {}", root_name(&self.roots, cell / 2))
        }
    }
}

/// The printed name of one `y`-cell of a cylinder.
fn y_cell_name(y_cell: usize, roots: usize, sample: &SamplePoint) -> String {
    if y_cell.is_multiple_of(2) {
        let k = y_cell / 2;
        let left = if k == 0 {
            "-∞".to_string()
        } else {
            format!("branch {k}")
        };
        let right = if k == roots {
            "∞".to_string()
        } else {
            format!("branch {}", k + 1)
        };
        format!("y ∈ ({left}, {right}) [sample {}]", sample_name(sample))
    } else {
        format!(
            "y = branch {} [sample {}]",
            y_cell / 2 + 1,
            sample_name(sample)
        )
    }
}

/// A cut point's printed name: itself when rational, `αk` otherwise.
fn root_name(roots: &[SamplePoint], index: usize) -> String {
    match &roots[index] {
        SamplePoint::Rational(value) => format_rational(value),
        SamplePoint::Algebraic { .. } => format!("α{}", index + 1),
    }
}

/// A sample's printed name.
fn sample_name(sample: &SamplePoint) -> String {
    match sample {
        SamplePoint::Rational(value) => format_rational(value),
        SamplePoint::Algebraic { lower, upper, .. } => {
            format!("in ({}, {}]", format_rational(lower), format_rational(upper))
        }
    }
}

/// `n` or `n/d`, never `n/1`.
fn format_rational(value: &BigRational) -> String {
    if value.denom().is_one() {
        format!("{}", value.numer())
    } else {
        format!("{}/{}", value.numer(), value.denom())
    }
}

/// The recomputed `y`-cut points match the recorded ones.
fn check_y_roots(
    cell: usize,
    recorded: &[SamplePoint],
    recomputed: &[SamplePoint],
) -> Result<(), Fault> {
    if recorded.len() != recomputed.len() {
        return Err(Fault::YRootsMismatch {
            cell,
            recorded: recorded.len(),
            recomputed: recomputed.len(),
        });
    }
    for (index, root) in recomputed.iter().enumerate() {
        if *root != recorded[index] {
            return Err(Fault::YRootValueMismatch { cell, index });
        }
    }
    Ok(())
}

// ============================================================================
// The producer.
// ============================================================================

/// Eliminate `z` from `∃z. ⋀ᵢ pᵢ(x, y, z) ▷ᵢ 0` and lift the `x`-line into a
/// cylindrical cell list over the `(x, y)`-plane.
///
/// ```
/// use axeyum_cas::qe::Relation;
/// use axeyum_cas::qe::lift::{ExistsZFormula, TriAtom, eliminate_z, tri_terms};
///
/// // ∃z. x·z = 1 ∧ y·z = 1 — true exactly on x = y ≠ 0.
/// let formula = ExistsZFormula::new(vec![
///     TriAtom::new(tri_terms(&[(1, 1, 0, 1), (-1, 0, 0, 0)]), Relation::Eq),
///     TriAtom::new(tri_terms(&[(1, 0, 1, 1), (-1, 0, 0, 0)]), Relation::Eq),
/// ]);
/// let certificate = eliminate_z(&formula).unwrap();
/// certificate.verify().unwrap();
/// assert!(certificate.is_total());
/// ```
///
/// # Errors
///
/// The [`Fault`] naming the bound, the degeneracy, or the decline that stopped
/// it. A successful return is a certificate, not a bare answer: call
/// [`LiftCertificate::verify`] on it. A cell whose `x`-sample is algebraic is
/// **not** an error; it is marked [`YLine::TowerDepthUnsupported`] and
/// [`LiftCertificate::is_total`] reports it.
pub fn eliminate_z(formula: &ExistsZFormula) -> Result<LiftCertificate, Fault> {
    check_degree_bound(&formula.atoms)?;
    let level_one = projection_z(&formula.atoms)?;
    let level_two = projection_y(&level_one)?;
    let cut = bivariate::projection_cut(&level_two);
    let isolated = bivariate::isolate_cut(&cut).map_err(lift_bivariate_fault)?;
    let roots: Vec<SamplePoint> = isolated
        .iter()
        .map(|root| SamplePoint::from_isolated(&cut, root))
        .collect();
    let open_samples = open_cell_samples(&cut, &isolated).map_err(Fault::Declined)?;

    let count = 2 * roots.len() + 1;
    let mut cells: Vec<XCell> = Vec::with_capacity(count);
    for cell in 0..count {
        let sample = if cell.is_multiple_of(2) {
            SamplePoint::Rational(open_samples[cell / 2].clone())
        } else {
            roots[cell / 2].clone()
        };
        let line = match &sample {
            SamplePoint::Algebraic { .. } => YLine::TowerDepthUnsupported,
            SamplePoint::Rational(x) => lift_cylinder(&formula.atoms, &level_one, cell, x)?,
        };
        cells.push(XCell { sample, line });
    }
    Ok(LiftCertificate {
        atoms: formula.atoms.clone(),
        projection_z: level_one,
        projection_y: level_two,
        cut,
        roots,
        cells,
    })
}

/// The self-checking front door: eliminate `z`, verify the certificate, and
/// hand back the cell list only if the checker accepted it.
///
/// # Errors
///
/// The [`Fault`] that stopped the producer, or the guard that refused its own
/// certificate.
pub fn eliminate_z_checked(formula: &ExistsZFormula) -> Result<LiftCertificate, Fault> {
    let certificate = eliminate_z(formula)?;
    certificate.verify()?;
    Ok(certificate)
}

/// The cylinder over one rational `x`-sample: decompose the `y`-line by the
/// level-1 set at `x`, then decide the `z`-fibre over every `y`-cell.
fn lift_cylinder(
    atoms: &[TriAtom],
    level_one: &[BigBiPoly],
    cell: usize,
    x: &BigRational,
) -> Result<YLine, Fault> {
    let fibre_atoms = y_line_atoms(level_one, x);
    let decomposition =
        decompose(&fibre_atoms).map_err(|reason| Fault::Declined(format!("cell {cell}: {reason}")))?;
    let roots: Vec<SamplePoint> = decomposition
        .roots
        .iter()
        .map(|root| SamplePoint::from_isolated(&decomposition.cut, root))
        .collect();
    let count = 2 * roots.len() + 1;
    let mut cells: Vec<PlaneCell> = Vec::with_capacity(count);
    for y_cell in 0..count {
        let sample = if y_cell.is_multiple_of(2) {
            SamplePoint::Rational(decomposition.open_samples[y_cell / 2].clone())
        } else {
            roots[y_cell / 2].clone()
        };
        cells.push(decide_plane_cell(
            atoms,
            cell,
            y_cell,
            x,
            &decomposition.cut,
            sample,
        )?);
    }
    Ok(YLine::Lifted { roots, cells })
}

/// One plane cell: the ℚ route at a rational `y`, the `ℚ(β)` route otherwise.
fn decide_plane_cell(
    atoms: &[TriAtom],
    cell: usize,
    y_cell: usize,
    x: &BigRational,
    y_cut: &[BigRational],
    sample: SamplePoint,
) -> Result<PlaneCell, Fault> {
    match &sample {
        SamplePoint::Rational(y) => {
            let decision = decide_exists(&ExistsFormula::new(substitute_xy(atoms, x, y)));
            let verdict = decision
                .verify()
                .map_err(|fault| Fault::Univariate {
                    cell,
                    y_cell,
                    fault,
                })?
                .ok_or_else(|| {
                    Fault::Declined(format!("the fibre over cell {cell}/{y_cell} declined"))
                })?;
            Ok(PlaneCell {
                sample,
                verdict,
                fibre: ZFibre::Rational(decision),
            })
        }
        SamplePoint::Algebraic { lower, upper, .. } => {
            let certificate = fibre::decide_fibre(y_cut, lower, upper, &substitute_x(atoms, x))
                .map_err(|fault| Fault::Fibre {
                    cell,
                    y_cell,
                    fault,
                })?;
            let verdict = certificate.verdict();
            Ok(PlaneCell {
                sample,
                verdict,
                fibre: ZFibre::Algebraic(Box::new(certificate)),
            })
        }
    }
}

// ============================================================================
// The degree bound.
// ============================================================================

/// Every atom is within [`MAX_TOTAL_DEGREE`].
fn check_degree_bound(atoms: &[TriAtom]) -> Result<(), Fault> {
    for (index, atom) in atoms.iter().enumerate() {
        let Some(total) = total_degree(&atom.poly) else {
            continue; // the zero polynomial
        };
        if total > MAX_TOTAL_DEGREE {
            return Err(Fault::DegreeBoundExceeded {
                atom: index,
                total_degree: total,
                bound: MAX_TOTAL_DEGREE,
            });
        }
    }
    Ok(())
}

/// `max (i + j + k)` over the nonzero monomials `xⁱ yʲ zᵏ`, or `None` for the
/// zero polynomial.
fn total_degree(p: &TriPoly) -> Option<usize> {
    let mut best: Option<usize> = None;
    for (z_power, level) in p.iter().enumerate() {
        for (y_power, row) in level.iter().enumerate() {
            if let Some(x_degree) = big::degree(row) {
                let total = z_power + y_power + x_degree;
                best = Some(best.map_or(total, |current: usize| current.max(total)));
            }
        }
    }
    best
}

// ============================================================================
// Bivariate coefficient arithmetic, over ℚ[x, y].
// ============================================================================

/// `a · b` in `ℚ[x][y]`, built from the bivariate step's own `bi_scale`,
/// `bi_shift` and `bi_add`.
fn bi_mul(a: &BigBiPoly, b: &BigBiPoly) -> BigBiPoly {
    let mut out: BigBiPoly = Vec::new();
    for (power, coefficient) in b.iter().enumerate() {
        if big::degree(coefficient).is_none() {
            continue;
        }
        out = bivariate::bi_add(&out, &bivariate::bi_shift(&bivariate::bi_scale(a, coefficient), power));
    }
    bi_trim(out)
}

/// Drop trailing zero `y`-coefficients.
fn bi_trim(mut p: BigBiPoly) -> BigBiPoly {
    while p.last().is_some_and(|c| big::degree(c).is_none()) {
        p.pop();
    }
    p
}

/// Whether every coefficient vanishes.
fn bi_is_zero(p: &BigBiPoly) -> bool {
    p.iter().all(|c| big::degree(c).is_none())
}

/// `1 ∈ ℚ[x, y]`.
fn bi_one() -> BigBiPoly {
    vec![vec![BigRational::one()]]
}

/// The lexicographically leading rational coefficient (highest `y`-power, then
/// highest `x`-power), or `None` for the zero polynomial.
fn leading_rational(p: &BigBiPoly) -> Option<BigRational> {
    for coefficient in p.iter().rev() {
        if let Some(degree) = big::degree(coefficient) {
            return Some(coefficient[degree].clone());
        }
    }
    None
}

/// The polynomial scaled to leading coefficient one, or `None` when it is zero
/// or a constant — a constant has no roots, so it cuts nothing.
fn canonical_bi(p: &BigBiPoly) -> Option<BigBiPoly> {
    let trimmed = bi_trim(p.to_vec());
    let leading = leading_rational(&trimmed)?;
    if trimmed.len() == 1 && big::degree(&trimmed[0]) == Some(0) {
        return None;
    }
    Some(
        trimmed
            .iter()
            .map(|c| big::trim(c.iter().map(|value| value / &leading).collect()))
            .collect(),
    )
}

// ============================================================================
// Level one: projecting `z` out, over the ring ℚ[x, y].
// ============================================================================

/// The `z`-degree, or `None` for the zero polynomial.
fn degree_z(p: &TriPoly) -> Option<usize> {
    p.iter().rposition(|c| !bi_is_zero(c))
}

/// The reducta of `p` in `z`: `p`, then `p` with its top `z`-term deleted, and
/// so on down to the `z`-free part.
fn reducta_z(p: &TriPoly) -> Vec<TriPoly> {
    let mut out: Vec<TriPoly> = Vec::new();
    let mut current: TriPoly = p.clone();
    loop {
        match degree_z(&current) {
            None => break,
            Some(0) => {
                out.push(vec![bi_trim(current[0].clone())]);
                break;
            }
            Some(k) => {
                let mut next = current.clone();
                next[k] = Vec::new();
                out.push(current[..=k].to_vec());
                current = next;
            }
        }
    }
    out
}

/// `∂p/∂z`.
fn derivative_z(p: &TriPoly) -> TriPoly {
    p.iter()
        .enumerate()
        .skip(1)
        .map(|(power, coefficient)| {
            let scale = vec![BigRational::from_integer(BigInt::from(power))];
            bivariate::bi_scale(coefficient, &scale)
        })
        .collect()
}

/// `res_z(p, q)` as a polynomial in `(x, y)`, by the Sylvester determinant over
/// the ring `ℚ[x, y]`. `None` when either has `z`-degree below one.
fn resultant_z(p: &TriPoly, q: &TriPoly) -> Option<BigBiPoly> {
    let p_degree = degree_z(p)?;
    let q_degree = degree_z(q)?;
    if p_degree == 0 || q_degree == 0 {
        return None;
    }
    let size = p_degree + q_degree;
    let mut matrix: Vec<Vec<BigBiPoly>> = vec![vec![Vec::new(); size]; size];
    for row in 0..q_degree {
        for (offset, coefficient) in p[..=p_degree].iter().rev().enumerate() {
            matrix[row][row + offset] = coefficient.clone();
        }
    }
    for row in 0..p_degree {
        for (offset, coefficient) in q[..=q_degree].iter().rev().enumerate() {
            matrix[q_degree + row][row + offset] = coefficient.clone();
        }
    }
    Some(ring_determinant(&matrix))
}

/// The determinant of a square matrix over `ℚ[x, y]`, by Laplace expansion over
/// column subsets with memoisation — `O(2ⁿ · n)` ring multiplications, and
/// `n ≤ 6` under [`MAX_TOTAL_DEGREE`]. No division is used, so this is valid
/// over any commutative ring.
fn ring_determinant(matrix: &[Vec<BigBiPoly>]) -> BigBiPoly {
    let size = matrix.len();
    if size == 0 {
        return bi_one();
    }
    let mut memo: BTreeMap<u64, BigBiPoly> = BTreeMap::new();
    let full: u64 = (1u64 << size) - 1;
    minor(matrix, full, size, &mut memo)
}

/// The determinant of the submatrix using the last `popcount(mask)` rows and
/// the columns in `mask`.
fn minor(
    matrix: &[Vec<BigBiPoly>],
    mask: u64,
    size: usize,
    memo: &mut BTreeMap<u64, BigBiPoly>,
) -> BigBiPoly {
    if mask == 0 {
        return bi_one();
    }
    if let Some(value) = memo.get(&mask) {
        return value.clone();
    }
    let row = size - (mask.count_ones() as usize);
    let mut total: BigBiPoly = Vec::new();
    let mut position = 0usize;
    for column in 0..size {
        if mask & (1u64 << column) == 0 {
            continue;
        }
        let entry = &matrix[row][column];
        position += 1;
        if bi_is_zero(entry) {
            continue;
        }
        let sub = minor(matrix, mask & !(1u64 << column), size, memo);
        let term = bi_mul(entry, &sub);
        total = if position.is_multiple_of(2) {
            bivariate::bi_sub(&total, &term)
        } else {
            bivariate::bi_add(&total, &term)
        };
    }
    let total = bi_trim(total);
    memo.insert(mask, total.clone());
    total
}

/// The level-1 projection set `PROJ_z(atoms)`: canonical, deduplicated, and
/// ordered deterministically by a [`std::collections::BTreeMap`] keyed on the
/// canonical polynomial itself.
fn projection_z(atoms: &[TriAtom]) -> Result<Vec<BigBiPoly>, Fault> {
    let mut set: BTreeMap<BigBiPoly, ()> = BTreeMap::new();
    let mut positive: BTreeMap<TriPoly, ()> = BTreeMap::new();
    for atom in atoms {
        for reductum in reducta_z(&atom.poly) {
            match degree_z(&reductum) {
                None => {}
                Some(0) => insert_projection(&mut set, &reductum[0]),
                Some(k) => {
                    insert_projection(&mut set, &reductum[k]);
                    if k >= 2 {
                        add_discriminant(&mut set, &reductum)?;
                    }
                    if let Some(key) = canonical_tri(&reductum) {
                        positive.insert(key, ());
                    }
                }
            }
        }
    }
    let unique: Vec<TriPoly> = positive.into_keys().collect();
    for i in 0..unique.len() {
        for j in (i + 1)..unique.len() {
            let resultant = resultant_z(&unique[i], &unique[j]).ok_or(Fault::Declined(
                "a pairwise z-resultant of positive-degree reducta was not defined".to_string(),
            ))?;
            if bi_is_zero(&resultant) {
                return Err(Fault::DegenerateProjection {
                    what: "a pairwise z-resultant vanishes identically",
                });
            }
            insert_projection(&mut set, &resultant);
        }
    }
    Ok(set.into_keys().collect())
}

/// The discriminant of one reductum of `z`-degree at least two.
fn add_discriminant(set: &mut BTreeMap<BigBiPoly, ()>, reductum: &TriPoly) -> Result<(), Fault> {
    let derivative = derivative_z(reductum);
    let discriminant = resultant_z(reductum, &derivative).ok_or(Fault::Declined(
        "the z-discriminant of a reductum was not defined".to_string(),
    ))?;
    if bi_is_zero(&discriminant) {
        return Err(Fault::DegenerateProjection {
            what: "a z-discriminant vanishes identically (a repeated z-factor)",
        });
    }
    insert_projection(set, &discriminant);
    Ok(())
}

/// Insert a candidate cut polynomial, canonical, dropping constants.
fn insert_projection(set: &mut BTreeMap<BigBiPoly, ()>, candidate: &BigBiPoly) {
    if let Some(canonical) = canonical_bi(candidate) {
        set.insert(canonical, ());
    }
}

/// A trivariate polynomial scaled to leading coefficient one, for
/// deduplication. `None` for the zero polynomial.
fn canonical_tri(p: &TriPoly) -> Option<TriPoly> {
    let degree = degree_z(p)?;
    let leading = leading_rational(&p[degree])?;
    Some(
        p[..=degree]
            .iter()
            .map(|level| {
                bi_trim(
                    level
                        .iter()
                        .map(|c| big::trim(c.iter().map(|value| value / &leading).collect()))
                        .collect(),
                )
            })
            .collect(),
    )
}

// ============================================================================
// Level two: projecting `y` out, through the bivariate step.
// ============================================================================

/// The level-2 projection set `PROJ_y(level_one)`, computed by
/// [`crate::qe::bivariate`]'s own projection operator.
///
/// The level-1 set is handed over on the `i128` surface that operator is
/// written against; a coefficient that does not fit is a named decline. The
/// bivariate module's **atom** degree bound is deliberately not applied: a
/// projection polynomial is not an atom, and Collins' operator is sound at any
/// degree.
fn projection_y(level_one: &[BigBiPoly]) -> Result<Vec<Vec<axeyum_ir::Rational>>, Fault> {
    let mut polys = Vec::with_capacity(level_one.len());
    for candidate in level_one {
        let small = bivariate::bipoly_of_big(candidate).ok_or(Fault::Declined(
            "a level-one projection polynomial does not fit the i128 surface".to_string(),
        ))?;
        polys.push(small);
    }
    bivariate::projection_set_of_polys(&polys).map_err(lift_bivariate_fault)
}

/// A bivariate fault as a lifting fault.
fn lift_bivariate_fault(fault: bivariate::Fault) -> Fault {
    match fault {
        bivariate::Fault::Declined(reason) => Fault::Declined(reason),
        other => Fault::LevelTwoProjection(Box::new(other)),
    }
}

// ============================================================================
// Substitution.
// ============================================================================

/// One bivariate coefficient with `x = x₀`: an LSB-first ℚ-polynomial in `y`.
fn eval_x(p: &BigBiPoly, x: &BigRational) -> Vec<BigRational> {
    big::trim(p.iter().map(|c| big::eval(c, x)).collect())
}

/// The level-1 set at `x = x₀`, as atoms whose roots cut the `y`-line. The
/// relation is immaterial: [`crate::qe::decompose`] reads only the polynomials.
fn y_line_atoms(level_one: &[BigBiPoly], x: &BigRational) -> Vec<Atom> {
    level_one
        .iter()
        .map(|candidate| Atom::new(eval_x(candidate, x), Relation::Eq))
        .collect()
}

/// The atoms with `x = x₀`, as the `ℚ(β)` fibre engine wants them: the `y`
/// polynomial multiplying each power of `z`.
fn substitute_x(atoms: &[TriAtom], x: &BigRational) -> Vec<fibre::SubstitutionAtom> {
    atoms
        .iter()
        .map(|atom| fibre::SubstitutionAtom {
            coefficients: atom.poly.iter().map(|level| eval_x(level, x)).collect(),
            relation: atom.relation,
        })
        .collect()
}

/// The atoms with `x = x₀` and `y = y₀`: univariate in `z` over ℚ.
fn substitute_xy(atoms: &[TriAtom], x: &BigRational, y: &BigRational) -> Vec<Atom> {
    atoms
        .iter()
        .map(|atom| {
            let coefficients: Vec<BigRational> = atom
                .poly
                .iter()
                .map(|level| big::eval(&eval_x(level, x), y))
                .collect();
            Atom::new(big::trim(coefficients), atom.relation)
        })
        .collect()
}

/// The atoms a univariate decision's certificate is about, or `None` for a
/// decline.
fn certificate_atoms(decision: &Decision) -> Option<Vec<Atom>> {
    match decision {
        Decision::True(cert) => Some(cert.atoms.clone()),
        Decision::False(cert) => Some(cert.atoms.clone()),
        Decision::Unknown(_) => None,
    }
}
