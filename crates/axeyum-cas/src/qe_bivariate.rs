//! One **bivariate projection step**: eliminate `y` from
//! `∃y. ⋀ᵢ pᵢ(x, y) ▷ᵢ 0` and return a quantifier-free description of the
//! `x`-line, cell by cell, with a certificate.
//!
//! # The method, and why one sample per cell suffices
//!
//! Collins' projection. From the atom set `A` we compute a set of polynomials
//! in `x` alone:
//!
//! - the **leading coefficient** `lc_y(r)` of every *reductum* `r` of every
//!   `pᵢ` (a reductum is `p` with its top `y`-terms successively deleted);
//! - the **discriminant** of every reductum of `y`-degree at least 2 — here as
//!   `res_y(r, ∂r/∂y)`, which is the true discriminant times `lc_y(r)`. That
//!   extra factor is already in the set, so using the undivided resultant only
//!   *refines* the decomposition, never coarsens it;
//! - the **resultant** `res_y(r, s)` of every pair of reducta coming from two
//!   different atoms;
//! - the `y`-free part of every atom, which is a condition on `x` alone.
//!
//! Let `C` be a cell of the `x`-line on which every one of those polynomials
//! has constant sign — in particular, none of them vanishes on `C` unless it
//! vanishes identically. Then every `pᵢ` is **delineable** over `C`:
//!
//! - no leading coefficient vanishes, so `deg_y pᵢ(x₀, y)` does not drop as
//!   `x₀` moves across `C` and no root escapes to infinity;
//! - no discriminant vanishes, so no two roots of a single `pᵢ(x₀, ·)` collide;
//! - no resultant vanishes, so a root of `pᵢ(x₀, ·)` never meets a root of
//!   `pⱼ(x₀, ·)`.
//!
//! The real roots of the `pᵢ` in `y` therefore form finitely many continuous,
//! non-crossing branches over `C`, so the sign vector of `(p₁, …, pₙ)` on each
//! `y`-cell is the same for every `x₀ ∈ C`. The truth of `∃y. ⋀ᵢ pᵢ ▷ᵢ 0` is a
//! function of that sign vector alone — hence **constant on `C`**, and one
//! sample `x₀ ∈ C` decides the whole cell.
//!
//! Point cells need no delineability argument at all: a point cell *is* a
//! single `x₀`, and we decide the fibre there exactly.
//!
//! # Which hypothesis the degree bound guarantees
//!
//! Collins' theorem needs the projection set to be **exhaustive**: every
//! reductum's leading coefficient and discriminant, and every pair of reducta.
//! (`McCallum`'s much smaller projection replaces that with an order-invariance
//! argument plus a "well-oriented" side condition that has to be *checked* and
//! can fail; we do not use it.) The bound
//! `total degree ≤ `[`MAX_TOTAL_DEGREE`] is what makes the exhaustive set
//! finite *and small*: `deg_y p ≤ 4`, so each atom has at most five reducta and
//! the pairwise-resultant stage stays inside the exact `i128`-rational Sylvester
//! determinant that [`axeyum_ir::poly::sylvester_determinant`] provides. A
//! larger degree is refused by name rather than attempted — see
//! [`Fault::DegreeBoundExceeded`].
//!
//! # What this step cannot do
//!
//! - **An irrational cell boundary.** A point cell sits at a root of a
//!   projection polynomial; deciding the fibre there means substituting that
//!   root for `x`, which turns the coefficients into elements of `ℚ(α)`. This
//!   slice has no `ℚ(α)` arithmetic, so an irrational projection root is a
//!   decline ([`Fault::IrrationalCellBoundary`]), not a guess. Every open cell
//!   is unaffected: its sample is rational by construction.
//! - **A degenerate projection.** If a resultant vanishes identically, two
//!   atoms share a factor of positive `y`-degree and the delineability argument
//!   above does not apply. That is refused
//!   ([`Fault::DegenerateProjection`]), not worked around.
//! - **Three variables, or a second quantifier.** There is no lifting phase and
//!   no cell adjacency structure, so this is a projection step, not a CAD.

use std::collections::BTreeMap;

use axeyum_ir::{Rational, poly};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use super::{Atom, Decision, ExistsFormula, Relation, big, big_poly, decide_exists};

/// The largest total degree this step accepts in any atom. See the module
/// documentation for what the bound buys.
pub const MAX_TOTAL_DEGREE: usize = 4;

/// A bivariate polynomial in `x` and `y`: `poly[j]` is the coefficient of `yʲ`,
/// itself an LSB-first polynomial in `x` over ℚ.
pub type BiPoly = Vec<Vec<Rational>>;

/// One bivariate atom `poly(x, y) ▷ 0`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BiAtom {
    /// The polynomial, as coefficients of powers of `y`.
    pub poly: BiPoly,
    /// The comparison against `0`.
    pub relation: Relation,
}

impl BiAtom {
    /// Build a bivariate atom.
    #[must_use]
    pub fn new(poly: BiPoly, relation: Relation) -> BiAtom {
        BiAtom { poly, relation }
    }
}

/// `∃y. ⋀ᵢ atoms[i]`, with `x` left free.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ExistsYFormula {
    /// The conjuncts. An **empty** conjunction is `true` everywhere.
    pub atoms: Vec<BiAtom>,
}

impl ExistsYFormula {
    /// Build `∃y. ⋀ atoms`.
    #[must_use]
    pub fn new(atoms: Vec<BiAtom>) -> ExistsYFormula {
        ExistsYFormula { atoms }
    }
}

/// Why a projection or its certificate was refused.
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
    /// A projection polynomial vanishes identically, so two atoms share a
    /// factor of positive `y`-degree and delineability does not apply.
    DegenerateProjection {
        /// What was being computed.
        what: &'static str,
    },
    /// The recomputed projection set is not the recorded one.
    ProjectionMismatch {
        /// Polynomials the certificate records.
        recorded: usize,
        /// Polynomials re-derived from the atoms.
        recomputed: usize,
    },
    /// The recorded cut points are not the real roots of the projection set.
    RootsMismatch {
        /// Roots the certificate records.
        recorded: usize,
        /// Roots re-derived from the projection set.
        recomputed: usize,
    },
    /// A recorded cut point is not the re-derived one at that position.
    RootValueMismatch {
        /// Which cut point.
        index: usize,
    },
    /// A projection root is irrational, so its point cell cannot be decided
    /// without arithmetic in `ℚ(α)`.
    IrrationalCellBoundary {
        /// Which cut point.
        index: usize,
    },
    /// The certificate records the wrong number of cells (`2r + 1` for `r` cut
    /// points).
    CellCountMismatch {
        /// Cells recorded.
        recorded: usize,
        /// Cells required.
        expected: usize,
    },
    /// A cell's recorded `x`-sample does not lie in that cell.
    CellSampleOutOfOrder {
        /// The offending cell.
        cell: usize,
    },
    /// A cell's univariate certificate is not about the substituted atoms, so
    /// it decides some other formula.
    SubstitutionMismatch {
        /// The offending cell.
        cell: usize,
    },
    /// A cell's recorded verdict is not the one its univariate certificate
    /// establishes.
    CellVerdictMismatch {
        /// The offending cell.
        cell: usize,
        /// The verdict recorded.
        recorded: bool,
        /// The verdict the certificate establishes.
        recomputed: bool,
    },
    /// A cell's univariate certificate was refused.
    Univariate {
        /// The offending cell.
        cell: usize,
        /// The univariate guard that rejected.
        fault: super::Fault,
    },
    /// Exact arithmetic declined — an `i128` overflow in the Sylvester
    /// determinant, or a step budget in the private `qe::big` engine. Not a refusal of any claim.
    Declined(String),
}

/// The decision for one `x`-cell: where it was sampled, what the answer is
/// there, and the univariate certificate that establishes it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CellCertificate {
    /// The rational `x` at which the fibre was decided.
    pub sample: BigRational,
    /// Whether `∃y. ⋀ᵢ pᵢ(sample, y) ▷ᵢ 0` holds.
    pub verdict: bool,
    /// The univariate decision in `y` at `sample`, certificate and all.
    pub decision: Decision,
}

/// The result of eliminating `y`: a description of the `x`-line as `2r + 1`
/// cells with a verdict each, and everything needed to re-derive it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectionCertificate {
    /// The formula this certificate is about.
    pub atoms: Vec<BiAtom>,
    /// The projection set, monic and deduplicated, in a deterministic order.
    pub projection: Vec<Vec<Rational>>,
    /// The cut points: the distinct real roots of the projection set,
    /// ascending. All rational — an irrational one is a decline.
    pub roots: Vec<BigRational>,
    /// One entry per cell, interleaved `(−∞, α₀)`, `{α₀}`, `(α₀, α₁)`, …
    pub cells: Vec<CellCertificate>,
}

impl ProjectionCertificate {
    /// Re-derive the whole elimination from `atoms` alone.
    ///
    /// Guards, in order: the degree bound still holds; the projection set
    /// recomputed from the atoms is exactly the recorded one; the cut points
    /// recomputed by isolating the projection set's roots are exactly the
    /// recorded ones, and all rational; the cell count matches; every cell's
    /// recorded `x`-sample really lies in that cell, in order; every cell's
    /// univariate certificate is about the atoms obtained by substituting that
    /// sample; and every one of those certificates verifies and establishes the
    /// recorded verdict.
    ///
    /// Nothing the producer computed is reused — not the projection, not the
    /// roots, not a single sign.
    ///
    /// # Errors
    ///
    /// The [`Fault`] naming the guard that rejected.
    pub fn verify(&self) -> Result<(), Fault> {
        check_degree_bound(&self.atoms)?;
        let recomputed = projection_set(&self.atoms)?;
        if recomputed != self.projection {
            return Err(Fault::ProjectionMismatch {
                recorded: self.projection.len(),
                recomputed: recomputed.len(),
            });
        }
        let roots = projection_roots(&recomputed)?;
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
        for (cell, entry) in self.cells.iter().enumerate() {
            check_sample_in_cell(&roots, cell, &entry.sample)?;
            let substituted = substitute_atoms(&self.atoms, &entry.sample);
            if certificate_atoms(&entry.decision) != Some(substituted) {
                return Err(Fault::SubstitutionMismatch { cell });
            }
            let verdict = entry
                .decision
                .verify()
                .map_err(|fault| Fault::Univariate { cell, fault })?
                .ok_or_else(|| {
                    Fault::Declined(format!("cell {cell} carries no univariate claim"))
                })?;
            if verdict != entry.verdict {
                return Err(Fault::CellVerdictMismatch {
                    cell,
                    recorded: entry.verdict,
                    recomputed: verdict,
                });
            }
        }
        Ok(())
    }

    /// The quantifier-free description, as a union of `x`-intervals and points.
    ///
    /// Adjacent true cells are merged, so `{0} ∪ (0, ∞)` prints as `[0, ∞)`.
    /// The empty set prints as `∅`. Call [`ProjectionCertificate::verify`]
    /// first: this reads the recorded verdicts.
    #[must_use]
    pub fn describe(&self) -> String {
        let runs = self.true_runs();
        if runs.is_empty() {
            return "∅".to_string();
        }
        let pieces: Vec<String> = runs
            .iter()
            .map(|(start, end)| self.format_run(*start, *end))
            .collect();
        format!("x ∈ {}", pieces.join(" ∪ "))
    }

    /// Maximal runs of consecutive cells whose verdict is `true`.
    fn true_runs(&self) -> Vec<(usize, usize)> {
        let mut runs: Vec<(usize, usize)> = Vec::new();
        let mut start: Option<usize> = None;
        for (index, cell) in self.cells.iter().enumerate() {
            match (cell.verdict, start) {
                (true, None) => start = Some(index),
                (false, Some(begin)) => {
                    runs.push((begin, index - 1));
                    start = None;
                }
                _ => {}
            }
        }
        if let Some(begin) = start {
            runs.push((begin, self.cells.len() - 1));
        }
        runs
    }

    /// One run of true cells as an interval or a point.
    fn format_run(&self, start: usize, end: usize) -> String {
        let last = self.roots.len();
        let (open_left, left) = if start.is_multiple_of(2) {
            let k = start / 2;
            if k == 0 {
                (true, "-∞".to_string())
            } else {
                (true, format_rational(&self.roots[k - 1]))
            }
        } else {
            (false, format_rational(&self.roots[start / 2]))
        };
        let (open_right, right) = if end.is_multiple_of(2) {
            let k = end / 2;
            if k == last {
                (true, "∞".to_string())
            } else {
                (true, format_rational(&self.roots[k]))
            }
        } else {
            (false, format_rational(&self.roots[end / 2]))
        };
        if !open_left && !open_right && left == right {
            return format!("{{{left}}}");
        }
        let lb = if open_left { '(' } else { '[' };
        let rb = if open_right { ')' } else { ']' };
        format!("{lb}{left}, {right}{rb}")
    }
}

/// Eliminate `y` from `∃y. ⋀ᵢ pᵢ(x, y) ▷ᵢ 0`.
///
/// ```
/// use axeyum_cas::qe::Relation;
/// use axeyum_cas::qe::bivariate::{BiAtom, ExistsYFormula, eliminate_y};
/// use axeyum_ir::Rational;
///
/// // ∃y. x² + y² − 1 < 0, i.e. y² + (x² − 1) < 0.
/// let zero = Rational::zero();
/// let one = Rational::integer(1);
/// let minus_one = Rational::integer(-1);
/// let atom = BiAtom::new(
///     vec![vec![minus_one, zero, one], vec![zero], vec![one]],
///     Relation::Lt,
/// );
/// let certificate = eliminate_y(&ExistsYFormula::new(vec![atom])).unwrap();
/// certificate.verify().unwrap();
/// assert_eq!(certificate.describe(), "x ∈ (-1, 1)");
/// ```
///
/// # Errors
///
/// The [`Fault`] naming the bound, the degeneracy, or the decline that stopped
/// it. A successful return is a certificate, not a bare answer: call
/// [`ProjectionCertificate::verify`] on it.
pub fn eliminate_y(formula: &ExistsYFormula) -> Result<ProjectionCertificate, Fault> {
    check_degree_bound(&formula.atoms)?;
    let projection = projection_set(&formula.atoms)?;
    let roots = projection_roots(&projection)?;
    let samples = cell_samples(&roots);

    let mut cells: Vec<CellCertificate> = Vec::with_capacity(samples.len());
    for (cell, sample) in samples.into_iter().enumerate() {
        let atoms = substitute_atoms(&formula.atoms, &sample);
        let decision = decide_exists(&ExistsFormula::new(atoms));
        let verdict = decision
            .verify()
            .map_err(|fault| Fault::Univariate { cell, fault })?
            .ok_or_else(|| {
                Fault::Declined(format!("the fibre over cell {cell} could not be decided"))
            })?;
        cells.push(CellCertificate {
            sample,
            verdict,
            decision,
        });
    }
    Ok(ProjectionCertificate {
        atoms: formula.atoms.clone(),
        projection,
        roots,
        cells,
    })
}

// ============================================================================
// The degree bound.
// ============================================================================

/// Every atom is within [`MAX_TOTAL_DEGREE`].
fn check_degree_bound(atoms: &[BiAtom]) -> Result<(), Fault> {
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

/// `max_j (j + deg_x poly[j])` over the nonzero `y`-coefficients, or `None` for
/// the zero polynomial.
#[must_use]
fn total_degree(p: &BiPoly) -> Option<usize> {
    let mut best: Option<usize> = None;
    for (power, coefficient) in p.iter().enumerate() {
        if let Some(x_degree) = poly::rat_degree(coefficient) {
            let total = power + x_degree;
            best = Some(best.map_or(total, |current: usize| current.max(total)));
        }
    }
    best
}

// ============================================================================
// The projection set.
// ============================================================================

/// The degree in `y`, or `None` for the zero polynomial.
#[must_use]
fn degree_y(p: &BiPoly) -> Option<usize> {
    p.iter().rposition(|c| poly::rat_degree(c).is_some())
}

/// A coefficient vector that is never empty, so the Sylvester builder always
/// sees a well-formed polynomial in `x`.
#[must_use]
fn normalise_x(p: &[Rational]) -> Vec<Rational> {
    if poly::rat_degree(p).is_none() {
        vec![Rational::zero()]
    } else {
        poly::rat_trim(p.to_vec())
    }
}

/// `∂p/∂y`.
#[must_use]
fn derivative_y(p: &BiPoly) -> Option<BiPoly> {
    let mut out: BiPoly = Vec::new();
    for (power, coefficient) in p.iter().enumerate().skip(1) {
        let scale = Rational::integer(i128::try_from(power).ok()?);
        let scaled: Option<Vec<Rational>> =
            coefficient.iter().map(|c| c.checked_mul(scale)).collect();
        out.push(scaled?);
    }
    Some(out)
}

/// The reducta of `p`: `p`, then `p` with its top `y`-term deleted, and so on
/// down to the `y`-free part.
#[must_use]
fn reducta(p: &BiPoly) -> Vec<BiPoly> {
    let mut out: Vec<BiPoly> = Vec::new();
    let mut current: BiPoly = p.clone();
    loop {
        match degree_y(&current) {
            None => break,
            Some(0) => {
                out.push(vec![normalise_x(&current[0])]);
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

/// `res_y(p, q)` as a polynomial in `x`, through the shared Sylvester engine in
/// [`axeyum_ir::poly`]. `None` when either has `y`-degree below 1, or on `i128`
/// overflow inside the determinant.
#[must_use]
fn resultant_y(p: &BiPoly, q: &BiPoly) -> Option<Vec<Rational>> {
    let p_degree = degree_y(p)?;
    let q_degree = degree_y(q)?;
    if p_degree == 0 || q_degree == 0 {
        return None;
    }
    let p_coeffs: Vec<Vec<Rational>> = p[..=p_degree].iter().map(|c| normalise_x(c)).collect();
    let q_coeffs: Vec<Vec<Rational>> = q[..=q_degree].iter().map(|c| normalise_x(c)).collect();
    let matrix = poly::sylvester_matrix(&p_coeffs, &q_coeffs)?;
    poly::sylvester_determinant(&matrix)
}

/// The polynomial made monic, or `None` if it is constant or zero (a constant
/// has no roots, so it cuts nothing and is dropped from the projection set).
#[must_use]
fn canonical(p: &[Rational]) -> Option<Vec<Rational>> {
    let degree = poly::rat_degree(p)?;
    if degree == 0 {
        return None;
    }
    let leading = p[degree];
    p[..=degree]
        .iter()
        .map(|c| c.checked_div(leading))
        .collect()
}

/// The sort key of a canonical polynomial: its coefficients as
/// `(numerator, denominator)` pairs. Deterministic and independent of hashing.
#[must_use]
fn projection_key(p: &[Rational]) -> Vec<(i128, i128)> {
    p.iter().map(|c| (c.numerator(), c.denominator())).collect()
}

/// The Collins projection set of `atoms`, monic, deduplicated, and ordered
/// deterministically.
///
/// # Errors
///
/// [`Fault::DegenerateProjection`] when a required resultant vanishes
/// identically, [`Fault::Declined`] on an `i128` overflow inside a Sylvester
/// determinant.
fn projection_set(atoms: &[BiAtom]) -> Result<Vec<Vec<Rational>>, Fault> {
    let mut set: BTreeMap<Vec<(i128, i128)>, Vec<Rational>> = BTreeMap::new();
    let mut insert = |candidate: &[Rational]| {
        if let Some(monic) = canonical(candidate) {
            set.insert(projection_key(&monic), monic);
        }
    };

    let mut positive_degree: Vec<BiPoly> = Vec::new();
    for atom in atoms {
        for reductum in reducta(&atom.poly) {
            match degree_y(&reductum) {
                None => {}
                Some(0) => insert(&reductum[0]),
                Some(k) => {
                    insert(&reductum[k]);
                    if k >= 2 {
                        let derivative = derivative_y(&reductum).ok_or_else(|| {
                            Fault::Declined("the y-derivative overflowed i128".to_string())
                        })?;
                        let discriminant =
                            resultant_y(&reductum, &derivative).ok_or_else(|| {
                                Fault::Declined(
                                    "a discriminant resultant overflowed i128".to_string(),
                                )
                            })?;
                        if poly::rat_degree(&discriminant).is_none() {
                            return Err(Fault::DegenerateProjection {
                                what: "the discriminant of an atom vanishes identically",
                            });
                        }
                        insert(&discriminant);
                    }
                    positive_degree.push(reductum);
                }
            }
        }
    }

    // Pairwise resultants across reducta of *different* atoms. Duplicates are
    // dropped first: `res_y(p, p)` is identically zero and carries nothing.
    let mut seen: BTreeMap<Vec<Vec<(i128, i128)>>, usize> = BTreeMap::new();
    let mut unique: Vec<BiPoly> = Vec::new();
    for reductum in positive_degree {
        let key: Vec<Vec<(i128, i128)>> = reductum.iter().map(|c| projection_key(c)).collect();
        if seen.insert(key, unique.len()).is_none() {
            unique.push(reductum);
        }
    }
    for i in 0..unique.len() {
        for j in (i + 1)..unique.len() {
            let resultant = resultant_y(&unique[i], &unique[j]).ok_or_else(|| {
                Fault::Declined("a pairwise resultant overflowed i128".to_string())
            })?;
            if poly::rat_degree(&resultant).is_none() {
                return Err(Fault::DegenerateProjection {
                    what: "a pairwise resultant vanishes identically",
                });
            }
            insert(&resultant);
        }
    }
    Ok(set.into_values().collect())
}

// ============================================================================
// Cut points and cell samples.
// ============================================================================

/// The distinct real roots of the whole projection set, ascending. All of them
/// must be rational; an irrational one is a decline, because its point cell
/// would need `ℚ(α)` arithmetic.
///
/// # Errors
///
/// [`Fault::IrrationalCellBoundary`] or [`Fault::Declined`].
fn projection_roots(projection: &[Vec<Rational>]) -> Result<Vec<BigRational>, Fault> {
    let mut product = vec![BigRational::one()];
    for candidate in projection {
        product = big::mul(&product, &big_poly(candidate));
    }
    if big::degree(&product).is_none_or(|d| d == 0) {
        return Ok(Vec::new());
    }
    let cut = big::squarefree_part(&product)
        .ok_or_else(|| Fault::Declined("the projection product is zero".to_string()))?;
    let isolated = big::isolate(&cut).ok_or_else(|| {
        Fault::Declined("root isolation ran out of its bisection budget".to_string())
    })?;
    let mut roots = Vec::with_capacity(isolated.len());
    for (index, root) in isolated.iter().enumerate() {
        if !root.exact {
            return Err(Fault::IrrationalCellBoundary { index });
        }
        roots.push(root.hi.clone());
    }
    Ok(roots)
}

/// One rational `x` per cell, interleaved: below the first cut point, the cut
/// point itself, the midpoint of each gap, …, above the last.
fn cell_samples(roots: &[BigRational]) -> Vec<BigRational> {
    if roots.is_empty() {
        return vec![BigRational::zero()];
    }
    let two = BigRational::from_integer(BigInt::from(2));
    let mut samples = Vec::with_capacity(2 * roots.len() + 1);
    samples.push(&roots[0] - BigRational::one());
    for (index, root) in roots.iter().enumerate() {
        samples.push(root.clone());
        let next = match roots.get(index + 1) {
            Some(next) => (root + next) / &two,
            None => root + BigRational::one(),
        };
        samples.push(next);
    }
    samples
}

/// The recorded sample of cell `cell` really lies in that cell.
fn check_sample_in_cell(
    roots: &[BigRational],
    cell: usize,
    sample: &BigRational,
) -> Result<(), Fault> {
    if cell.is_multiple_of(2) {
        let k = cell / 2;
        let above_previous = k == 0 || *sample > roots[k - 1];
        let below_next = k == roots.len() || *sample < roots[k];
        if above_previous && below_next {
            return Ok(());
        }
    } else if roots.get(cell / 2) == Some(sample) {
        return Ok(());
    }
    Err(Fault::CellSampleOutOfOrder { cell })
}

// ============================================================================
// Substitution.
// ============================================================================

/// `pᵢ(x₀, y)` for every atom: each `y`-coefficient, a polynomial in `x`, is
/// evaluated at the rational `x₀` in `BigRational`.
fn substitute_atoms(atoms: &[BiAtom], x: &BigRational) -> Vec<Atom> {
    atoms
        .iter()
        .map(|atom| {
            let coefficients: Vec<BigRational> = atom
                .poly
                .iter()
                .map(|coefficient| big::eval(&big_poly(coefficient), x))
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

/// `n` or `n/d`, never `n/1`.
fn format_rational(value: &BigRational) -> String {
    if value.denom().is_one() {
        format!("{}", value.numer())
    } else {
        format!("{}/{}", value.numer(), value.denom())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(n: i128) -> Rational {
        Rational::integer(n)
    }

    /// A bivariate polynomial from `y`-coefficients given as integer `x`-polys.
    fn bipoly(coefficients: &[&[i128]]) -> BiPoly {
        coefficients
            .iter()
            .map(|c| c.iter().copied().map(r).collect())
            .collect()
    }

    fn atom(coefficients: &[&[i128]], relation: Relation) -> BiAtom {
        BiAtom::new(bipoly(coefficients), relation)
    }

    fn decided(atoms: Vec<BiAtom>) -> ProjectionCertificate {
        let certificate =
            eliminate_y(&ExistsYFormula::new(atoms)).expect("the projection must succeed");
        certificate.verify().expect("the certificate must verify");
        certificate
    }

    // ------------------------------------------------------------- verdicts

    #[test]
    fn the_unit_disc_projects_to_the_open_interval_minus_one_to_one() {
        // ∃y. x² + y² − 1 < 0  →  y² + (x² − 1) < 0.
        let certificate = decided(vec![atom(&[&[-1, 0, 1], &[0], &[1]], Relation::Lt)]);
        assert_eq!(certificate.describe(), "x ∈ (-1, 1)");
        assert_eq!(certificate.roots.len(), 2, "the cut points are ±1");
        assert_eq!(certificate.cells.len(), 5);
        assert_eq!(
            certificate
                .cells
                .iter()
                .map(|c| c.verdict)
                .collect::<Vec<_>>(),
            vec![false, false, true, false, false]
        );
    }

    #[test]
    fn the_parabola_y_squared_equals_x_projects_to_the_closed_half_line() {
        // ∃y. y² − x = 0.
        let certificate = decided(vec![atom(&[&[0, -1], &[0], &[1]], Relation::Eq)]);
        assert_eq!(certificate.describe(), "x ∈ [0, ∞)");
    }

    #[test]
    fn adding_y_positive_opens_the_half_line_at_zero() {
        // ∃y. y² − x = 0 ∧ y > 0.
        let certificate = decided(vec![
            atom(&[&[0, -1], &[0], &[1]], Relation::Eq),
            atom(&[&[0], &[1]], Relation::Gt),
        ]);
        assert_eq!(certificate.describe(), "x ∈ (0, ∞)");
    }

    #[test]
    fn the_hyperbola_xy_equals_one_with_y_positive_projects_to_the_positive_half_line() {
        // ∃y. x·y − 1 = 0 ∧ y > 0.  The leading `y`-coefficient is `x`, so the
        // degree drop at x = 0 is exactly what the projection's leading
        // coefficient catches.
        let certificate = decided(vec![
            atom(&[&[-1], &[0, 1]], Relation::Eq),
            atom(&[&[0], &[1]], Relation::Gt),
        ]);
        assert_eq!(certificate.describe(), "x ∈ (0, ∞)");
        assert_eq!(certificate.roots, vec![BigRational::zero()]);
    }

    #[test]
    fn an_empty_conjunction_is_true_on_the_whole_line() {
        let certificate = decided(Vec::new());
        assert_eq!(certificate.describe(), "x ∈ (-∞, ∞)");
        assert_eq!(certificate.cells.len(), 1);
    }

    #[test]
    fn a_condition_on_x_alone_still_cuts_the_line() {
        // ∃y. x − 2 > 0 — no `y` at all; the `y`-free part must reach the
        // projection set or the cut at 2 is lost.
        let certificate = decided(vec![atom(&[&[-2, 1]], Relation::Gt)]);
        assert_eq!(certificate.describe(), "x ∈ (2, ∞)");
    }

    #[test]
    fn a_single_point_cell_prints_as_a_singleton() {
        // ∃y. (x² − 1 = 0) ∧ (x + 1 > 0) — true only at x = 1.
        let certificate = decided(vec![
            atom(&[&[-1, 0, 1]], Relation::Eq),
            atom(&[&[1, 1]], Relation::Gt),
        ]);
        assert_eq!(certificate.describe(), "x ∈ {1}");
    }

    // ---------------------------------------------------------- the bound

    #[test]
    fn a_degree_five_atom_is_refused_by_the_bound_and_not_attempted() {
        // ∃y. y⁵ − x = 0 has total degree 5.
        let formula = ExistsYFormula::new(vec![atom(
            &[&[0, -1], &[0], &[0], &[0], &[0], &[1]],
            Relation::Eq,
        )]);
        assert_eq!(
            eliminate_y(&formula),
            Err(Fault::DegreeBoundExceeded {
                atom: 0,
                total_degree: 5,
                bound: MAX_TOTAL_DEGREE
            })
        );
        // The positive control: the same shape at degree 4 is accepted.
        let quartic = ExistsYFormula::new(vec![atom(
            &[&[0, -1], &[0], &[0], &[0], &[1]],
            Relation::Eq,
        )]);
        assert!(eliminate_y(&quartic).is_ok());
    }

    #[test]
    fn total_degree_counts_x_and_y_together() {
        // x²y² is total degree 4, not 2.
        assert_eq!(total_degree(&bipoly(&[&[0], &[0], &[0, 0, 1]])), Some(4));
        assert_eq!(total_degree(&bipoly(&[&[0]])), None);
    }

    // ------------------------------------------------------------ forgeries

    #[test]
    fn a_certificate_with_a_dropped_projection_polynomial_is_refused() {
        let mut certificate = decided(vec![atom(&[&[-1, 0, 1], &[0], &[1]], Relation::Lt)]);
        let recomputed = certificate.projection.len();
        certificate.projection.pop();
        assert_eq!(
            certificate.verify(),
            Err(Fault::ProjectionMismatch {
                recorded: recomputed - 1,
                recomputed
            })
        );
    }

    #[test]
    fn a_certificate_that_drops_a_cut_point_is_refused() {
        let mut certificate = decided(vec![atom(&[&[-1, 0, 1], &[0], &[1]], Relation::Lt)]);
        certificate.roots.pop();
        certificate.cells.truncate(3);
        assert_eq!(
            certificate.verify(),
            Err(Fault::RootsMismatch {
                recorded: 1,
                recomputed: 2
            })
        );
    }

    #[test]
    fn a_certificate_whose_sample_leaves_its_cell_is_refused() {
        let mut certificate = decided(vec![atom(&[&[-1, 0, 1], &[0], &[1]], Relation::Lt)]);
        // Cell 0 is (−∞, −1); 5 is not in it.
        certificate.cells[0].sample = BigRational::from_integer(BigInt::from(5));
        assert_eq!(
            certificate.verify(),
            Err(Fault::CellSampleOutOfOrder { cell: 0 })
        );
    }

    #[test]
    fn a_certificate_that_flips_a_cell_verdict_is_refused() {
        let mut certificate = decided(vec![atom(&[&[-1, 0, 1], &[0], &[1]], Relation::Lt)]);
        certificate.cells[2].verdict = false;
        assert_eq!(
            certificate.verify(),
            Err(Fault::CellVerdictMismatch {
                cell: 2,
                recorded: false,
                recomputed: true
            })
        );
    }

    #[test]
    fn a_certificate_whose_fibre_is_about_another_formula_is_refused() {
        let mut certificate = decided(vec![atom(&[&[-1, 0, 1], &[0], &[1]], Relation::Lt)]);
        // Swap in the fibre from the satisfying cell, keeping the sample: the
        // certificate now verifies on its own but is about the wrong formula.
        let borrowed = certificate.cells[2].decision.clone();
        certificate.cells[0].decision = borrowed;
        certificate.cells[0].verdict = true;
        assert_eq!(
            certificate.verify(),
            Err(Fault::SubstitutionMismatch { cell: 0 })
        );
    }

    #[test]
    fn a_certificate_with_the_wrong_number_of_cells_is_refused() {
        let mut certificate = decided(vec![atom(&[&[-1, 0, 1], &[0], &[1]], Relation::Lt)]);
        certificate.cells.pop();
        assert_eq!(
            certificate.verify(),
            Err(Fault::CellCountMismatch {
                recorded: 4,
                expected: 5
            })
        );
    }

    #[test]
    fn a_certificate_with_a_forged_fibre_certificate_is_refused_by_the_univariate_checker() {
        let mut certificate = decided(vec![atom(&[&[-1, 0, 1], &[0], &[1]], Relation::Lt)]);
        let Decision::True(cert) = &mut certificate.cells[2].decision else {
            panic!("cell 2 is the satisfying one");
        };
        cert.signs[0] = -cert.signs[0];
        assert!(matches!(
            certificate.verify(),
            Err(Fault::Univariate { cell: 2, .. })
        ));
    }

    // ------------------------------------------------------------ degeneracy

    #[test]
    fn two_atoms_sharing_a_factor_are_refused_rather_than_projected() {
        // ∃y. (y² − x = 0) ∧ (2y² − 2x > 0): the resultant of the two vanishes
        // identically, so delineability does not apply.
        let formula = ExistsYFormula::new(vec![
            atom(&[&[0, -1], &[0], &[1]], Relation::Eq),
            atom(&[&[0, -2], &[0], &[2]], Relation::Gt),
        ]);
        assert!(matches!(
            eliminate_y(&formula),
            Err(Fault::DegenerateProjection { .. })
        ));
    }
}
