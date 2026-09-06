//! One **bivariate projection step**: eliminate `y` from
//! `∃y. ⋀ᵢ pᵢ(x, y) ▷ᵢ 0` and return a quantifier-free description of the
//! `x`-line — as cells, and as a **union of intervals with algebraic
//! endpoints** — with a certificate.
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
//! - the **resultant** `res_y(r, s)` of every pair of distinct reducta;
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
//! ## A reductum with a repeated `y`-factor
//!
//! `res_y(r, ∂r/∂y)` vanishes **identically** exactly when `r` has a repeated
//! factor in `y` — `(y − x)²` is the smallest example. Such an `r` is not
//! degenerate; its *branches* are perfectly well behaved, there are simply
//! fewer of them than `deg_y r` suggests. So when the discriminant vanishes
//! identically the square-free part of `r` in `y` is formed (by a
//! pseudo-remainder gcd over `ℚ[x]`, exact and in `BigRational`, see
//! `y_squarefree_part`) and *its* discriminant is used instead: distinct
//! branches of `r` collide exactly where that one vanishes. A square-free part
//! of `y`-degree at most one describes a single branch, which cannot collide
//! with itself, and contributes nothing. The pseudo-division leaves the result
//! multiplied by some `c(x) ∈ ℚ[x]`; that only adds `c`'s roots as extra cut
//! points, which **refines** the decomposition and is therefore sound.
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
//! # Irrational cell boundaries
//!
//! A projection root that is not rational is **no longer a decline**. Its point
//! cell is decided by substituting `x = α` into the atoms, which turns their
//! `y`-coefficients into elements of `K = ℚ(α)`, and deciding the resulting
//! univariate problem *over `K`* — Sturm chains, real-root isolation and sign
//! determination all carried out with exact `ℚ(α)` arithmetic in
//! [`crate::qe::fibre`]. The certificate for such a cell records `α` (a
//! square-free divisor of the projection's cut polynomial, plus the isolating
//! bracket), the substituted `K`-polynomials, and the fibre's own witness; its
//! checker re-substitutes, re-derives every sign at `α` by its own bracket
//! refinement, and re-checks every relation.
//!
//! # The quantifier-free formula
//!
//! [`eliminate_y_to_formula`] turns the cell list into what a caller actually
//! wants: a disjunction of `x`-conditions with algebraic endpoints
//! ([`XInterval`]), adjacent true cells merged into one interval. Its
//! certificate re-derives the cell list and then checks the merge four ways —
//! every endpoint is a projection root, the intervals ascend and are disjoint,
//! the cells they cover are **exactly** the true cells, and no two of them
//! could have been merged further.
//!
//! # What is decided now, and what is not
//!
//! **Decided.** One projection step of `∃y. ⋀ᵢ pᵢ(x, y) ▷ᵢ 0` at total degree
//! at most [`MAX_TOTAL_DEGREE`], over **any** cell of the resulting `x`-line:
//! open cells at rational samples through the ℚ engine, point cells at rational
//! cut points likewise, and point cells at **irrational** cut points through
//! `ℚ(α)`. Both are certificate-carrying, and the output is either the cell
//! list ([`eliminate_y`]) or a quantifier-free union of intervals
//! ([`eliminate_y_to_formula`]) whose endpoints may be algebraic. An atom with
//! a repeated factor in `y` is handled rather than refused.
//!
//! **Not decided.** More than two variables — there is no lifting phase, so a
//! cell of this line cannot be lifted into a cell of the plane and projected
//! again. Any quantifier alternation: `∃x∀y` and `∀x∃y` have no representation
//! here, and the merged interval list is a description of one free variable's
//! truth set, not an input the module can quantify over again. Two atoms
//! sharing a factor of positive `y`-degree, which is still
//! [`Fault::DegenerateProjection`]. And nothing transcendental.
//!
//! # What this step still cannot do
//!
//! - **A degenerate projection.** If a pairwise resultant vanishes identically,
//!   two atoms share a factor of positive `y`-degree and the delineability
//!   argument above does not apply. That is refused
//!   ([`Fault::DegenerateProjection`]), not worked around.
//! - **Three variables, or a second quantifier.** There is a cell adjacency
//!   structure now, but only along one line; there is no lifting phase, so this
//!   is still a projection step and not a CAD.
//!
//! # Cost profile — ADVISORY
//!
//! Measured 2026-09-05, 3 repeats of a prebuilt `--release` lib-test binary at
//! load average 14–17 on a shared box; spread under 10% across repeats.
//! **Advisory only** — do not ratchet on these. Each row is one named test, and
//! every test runs the producer *and* a full independent `verify`.
//!
//! | shape | cost |
//! |---|---|
//! | degree 2, rational boundaries (`x² + y² < 1`) | under 1 ms |
//! | degree 4, rational boundaries (`x²y² − 1 < 0 ∧ y > 0`) | under 1 ms |
//! | degree 2, **irrational** boundaries (`x² + y² = 2 ∧ y > 0`), two point cells over `ℚ(√2)` | 42 ms |
//! | degree 4 total, one point cell over `ℚ(∛2)` (`(y − x)² ≤ 0 ∧ x³ = 2`) | 57 ms |
//! | degree 3 field, `y` algebraic **over** `K` (`y² = x ∧ x³ = 2`) | 90 ms |
//!
//! An irrational boundary costs roughly **60× a rational one at the same
//! degree**. The multiplier is not the cell count and not the field degree in
//! itself: it is that every coefficient comparison inside a Sturm chain over
//! `K` is a sign at `α` rather than a sign of a rational, and every
//! `K`-remainder needs an inverse modulo the modulus. The `ℚ(√2)` row carries
//! *two* algebraic cells and still costs less than the two `ℚ(∛2)` rows, whose
//! fibre roots are not elements of `K`.

use std::collections::BTreeMap;

use axeyum_ir::{Rational, poly};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use super::{
    Atom, Decision, ExistsFormula, Relation, SamplePoint, big, big_poly,
    compare_sample_to_rational, decide_exists, fibre, open_cell_samples, rational_of_big,
};

/// The largest total degree this step accepts in any atom. See the module
/// documentation for what the bound buys.
pub const MAX_TOTAL_DEGREE: usize = 4;

/// How many pseudo-remainder steps [`y_squarefree_part`] will take before
/// declining. The `y`-degree drops at every step, so [`MAX_TOTAL_DEGREE`]
/// already bounds it; this is the constant that makes the loop obviously
/// finite.
const MAX_PSEUDO_STEPS: usize = 64;

/// A bivariate polynomial in `x` and `y`: `poly[j]` is the coefficient of `yʲ`,
/// itself an LSB-first polynomial in `x` over ℚ.
pub type BiPoly = Vec<Vec<Rational>>;

/// The same shape over [`num_rational::BigRational`], used where the exact
/// pseudo-division would otherwise overflow `i128`, and by
/// [`crate::qe::lift`] as the coefficient ring `ℚ[x, y]` of the level-one
/// projection.
pub type BigBiPoly = Vec<Vec<BigRational>>;

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
    /// The recomputed cut polynomial — the square-free part of the projection
    /// set's product, which defines every algebraic cut point — is not the
    /// recorded one.
    CutMismatch {
        /// The degree recorded.
        recorded: usize,
        /// The degree re-derived.
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
    /// A cell's fibre certificate is of the wrong kind for its sample: a
    /// rational sample needs the ℚ route and an algebraic one the `ℚ(α)` route.
    FibreKindMismatch {
        /// The offending cell.
        cell: usize,
    },
    /// An algebraic cell's fibre certificate names a different bracket than the
    /// cut point it is supposed to be about, so it speaks about another `α`.
    FibreBracketMismatch {
        /// The offending cell.
        cell: usize,
    },
    /// An algebraic cell's fibre modulus does not divide the cut polynomial, so
    /// the `α` it presents need not be a projection root at all.
    ModulusNotADivisor {
        /// The offending cell.
        cell: usize,
    },
    /// A cell's fibre certificate is not about the substituted atoms, so it
    /// decides some other formula.
    SubstitutionMismatch {
        /// The offending cell.
        cell: usize,
    },
    /// A cell's recorded verdict is not the one its fibre certificate
    /// establishes.
    CellVerdictMismatch {
        /// The offending cell.
        cell: usize,
        /// The verdict recorded.
        recorded: bool,
        /// The verdict the certificate establishes.
        recomputed: bool,
    },
    /// A cell's univariate (rational-`x`) certificate was refused.
    Univariate {
        /// The offending cell.
        cell: usize,
        /// The univariate guard that rejected.
        fault: super::Fault,
    },
    /// A cell's `ℚ(α)` fibre certificate was refused.
    Fibre {
        /// The offending cell.
        cell: usize,
        /// The fibre guard that rejected.
        fault: fibre::Fault,
    },
    /// An interval endpoint is not one of the projection's cut points, so the
    /// formula speaks about a boundary the decomposition never produced.
    IntervalEndpointNotARoot {
        /// The offending interval.
        interval: usize,
    },
    /// The intervals are not strictly ascending and disjoint.
    IntervalOrderViolation {
        /// The offending interval.
        interval: usize,
    },
    /// A cell is covered by the intervals but false there, or true there and
    /// not covered — the guard that stops a merged interval from swallowing a
    /// false cell.
    IntervalCoverageMismatch {
        /// The offending cell.
        cell: usize,
        /// Whether the intervals cover it.
        covered: bool,
        /// The cell's verdict.
        verdict: bool,
    },
    /// Two consecutive intervals are contiguous and should have been one, so
    /// the recorded intervals are not maximal.
    IntervalsNotMerged {
        /// The interval that should have been merged with its predecessor.
        interval: usize,
    },
    /// Exact arithmetic declined — an `i128` overflow in the Sylvester
    /// determinant, or a step budget in the private `qe::big` engine. Not a
    /// refusal of any claim.
    Declined(String),
}

/// How one cell's fibre was decided.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CellFibre {
    /// The `x`-sample is rational, so the fibre is an ordinary univariate
    /// problem over ℚ.
    Rational(Decision),
    /// The `x`-sample is a real algebraic `α`, so the fibre was decided in
    /// `ℚ(α)`.
    Algebraic(Box<fibre::FibreCertificate>),
}

/// The decision for one `x`-cell: where it was sampled, what the answer is
/// there, and the fibre certificate that establishes it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CellCertificate {
    /// The `x` at which the fibre was decided — rational for an open cell, the
    /// cut point itself for a point cell.
    pub sample: SamplePoint,
    /// Whether `∃y. ⋀ᵢ pᵢ(sample, y) ▷ᵢ 0` holds.
    pub verdict: bool,
    /// The fibre decision in `y` at `sample`, certificate and all.
    pub fibre: CellFibre,
}

/// One maximal `x`-interval on which the eliminated formula holds. An endpoint
/// is `None` for an infinity and otherwise a **cut point**, which may be
/// algebraic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct XInterval {
    /// The left endpoint, or `None` for `−∞`.
    pub lower: Option<SamplePoint>,
    /// Whether the left endpoint is included.
    pub lower_closed: bool,
    /// The right endpoint, or `None` for `+∞`.
    pub upper: Option<SamplePoint>,
    /// Whether the right endpoint is included.
    pub upper_closed: bool,
}

/// The result of eliminating `y`: a description of the `x`-line as `2r + 1`
/// cells with a verdict each, and everything needed to re-derive it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectionCertificate {
    /// The formula this certificate is about.
    pub atoms: Vec<BiAtom>,
    /// The projection set, monic and deduplicated, in a deterministic order.
    pub projection: Vec<Vec<Rational>>,
    /// The **cut polynomial**: the square-free part of the projection set's
    /// product. It is the defining polynomial of every algebraic cut point.
    pub cut: Vec<BigRational>,
    /// The cut points: the distinct real roots of the cut polynomial,
    /// ascending. A rational one is exact; an irrational one is carried as an
    /// isolating bracket.
    pub roots: Vec<SamplePoint>,
    /// One entry per cell, interleaved `(−∞, α₀)`, `{α₀}`, `(α₀, α₁)`, …
    pub cells: Vec<CellCertificate>,
}

impl ProjectionCertificate {
    /// Re-derive the whole elimination from `atoms` alone.
    ///
    /// Guards, in order: the degree bound still holds; the projection set
    /// recomputed from the atoms is exactly the recorded one; so is the cut
    /// polynomial; the cut points recomputed by isolating its roots are exactly
    /// the recorded ones; the cell count matches; every cell's recorded
    /// `x`-sample really lies in that cell, in order; every cell's fibre
    /// certificate is of the right kind, is about the atoms obtained by
    /// substituting that sample, and establishes the recorded verdict.
    ///
    /// Nothing the producer computed is reused — not the projection, not the
    /// roots, not a single sign, and for an algebraic cell not the substituted
    /// `ℚ(α)` coefficients either.
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
        let cut = projection_cut(&recomputed);
        if cut != self.cut {
            return Err(Fault::CutMismatch {
                recorded: big::degree(&self.cut).unwrap_or(0),
                recomputed: big::degree(&cut).unwrap_or(0),
            });
        }
        let roots = cut_points(&cut)?;
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
            let verdict = self.check_fibre(cell, entry)?;
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

    /// One cell's fibre certificate: right kind, right formula, own verdict.
    fn check_fibre(&self, cell: usize, entry: &CellCertificate) -> Result<bool, Fault> {
        match (&entry.sample, &entry.fibre) {
            (SamplePoint::Rational(x), CellFibre::Rational(decision)) => {
                let substituted = substitute_atoms(&self.atoms, x);
                if certificate_atoms(decision) != Some(substituted) {
                    return Err(Fault::SubstitutionMismatch { cell });
                }
                decision
                    .verify()
                    .map_err(|fault| Fault::Univariate { cell, fault })?
                    .ok_or_else(|| {
                        Fault::Declined(format!("cell {cell} carries no univariate claim"))
                    })
            }
            (
                SamplePoint::Algebraic {
                    lower,
                    upper,
                    defining_poly,
                },
                CellFibre::Algebraic(certificate),
            ) => self.check_algebraic_fibre(cell, defining_poly, lower, upper, certificate),
            _ => Err(Fault::FibreKindMismatch { cell }),
        }
    }

    /// The `ℚ(α)` route's extra obligations: the recorded modulus really
    /// presents *this* cut point, and the substituted atoms are the ones the
    /// checker itself derives.
    fn check_algebraic_fibre(
        &self,
        cell: usize,
        defining_poly: &[BigRational],
        lower: &BigRational,
        upper: &BigRational,
        certificate: &fibre::FibreCertificate,
    ) -> Result<bool, Fault> {
        if certificate.lower != *lower || certificate.upper != *upper {
            return Err(Fault::FibreBracketMismatch { cell });
        }
        // `modulus | cut` plus "exactly one root of `modulus` in the bracket"
        // (checked inside `RealField::new`) forces that root to be this very
        // cut point, because the bracket isolates one root of `cut`.
        if !divides(&certificate.modulus, defining_poly) {
            return Err(Fault::ModulusNotADivisor { cell });
        }
        let field = fibre::RealField::new(&certificate.modulus, lower, upper)
            .map_err(|fault| Fault::Fibre { cell, fault })?;
        let substituted = fibre::substitute(&field, &substitution_atoms(&self.atoms));
        if certificate.atoms != substituted {
            return Err(Fault::SubstitutionMismatch { cell });
        }
        certificate
            .verify()
            .map_err(|fault| Fault::Fibre { cell, fault })
    }

    /// The quantifier-free description, as a union of `x`-intervals and points.
    ///
    /// Adjacent true cells are merged, so `{0} ∪ (0, ∞)` prints as `[0, ∞)`. An
    /// irrational cut point prints as `α1`, `α2`, … in ascending order; see
    /// [`ProjectionCertificate::legend`] for what those name. The empty set
    /// prints as `∅`. Call [`ProjectionCertificate::verify`] first: this reads
    /// the recorded verdicts.
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

    /// What each `αk` in [`ProjectionCertificate::describe`] names: its
    /// defining polynomial and its isolating bracket. Rational cut points do
    /// not appear, because they print as themselves.
    #[must_use]
    pub fn legend(&self) -> Vec<String> {
        let mut out = Vec::new();
        for (index, root) in self.roots.iter().enumerate() {
            if let SamplePoint::Algebraic {
                defining_poly,
                lower,
                upper,
            } = root
            {
                out.push(format!(
                    "α{} = the root of {} in ({}, {}]",
                    index + 1,
                    format_poly(defining_poly),
                    format_rational(lower),
                    format_rational(upper)
                ));
            }
        }
        out
    }

    /// The merged intervals: one per maximal run of true cells.
    #[must_use]
    pub fn intervals(&self) -> Vec<XInterval> {
        self.true_runs()
            .into_iter()
            .map(|(start, end)| self.interval_of_run(start, end))
            .collect()
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

    /// The interval a run of cells `start..=end` denotes.
    pub(super) fn interval_of_run(&self, start: usize, end: usize) -> XInterval {
        let (lower, lower_closed) = if start == 0 {
            (None, false)
        } else if start.is_multiple_of(2) {
            (Some(self.roots[start / 2 - 1].clone()), false)
        } else {
            (Some(self.roots[start / 2].clone()), true)
        };
        let (upper, upper_closed) = if end == 2 * self.roots.len() {
            (None, false)
        } else if end.is_multiple_of(2) {
            (Some(self.roots[end / 2].clone()), false)
        } else {
            (Some(self.roots[end / 2].clone()), true)
        };
        XInterval {
            lower,
            lower_closed,
            upper,
            upper_closed,
        }
    }

    /// One run of true cells as an interval or a point.
    pub(super) fn format_run(&self, start: usize, end: usize) -> String {
        let last = self.roots.len();
        let (open_left, left) = if start.is_multiple_of(2) {
            let k = start / 2;
            if k == 0 {
                (true, "-∞".to_string())
            } else {
                (true, self.root_name(k - 1))
            }
        } else {
            (false, self.root_name(start / 2))
        };
        let (open_right, right) = if end.is_multiple_of(2) {
            let k = end / 2;
            if k == last {
                (true, "∞".to_string())
            } else {
                (true, self.root_name(k))
            }
        } else {
            (false, self.root_name(end / 2))
        };
        if !open_left && !open_right && left == right {
            return format!("{{{left}}}");
        }
        let lb = if open_left { '(' } else { '[' };
        let rb = if open_right { ')' } else { ']' };
        format!("{lb}{left}, {right}{rb}")
    }

    /// A cut point's printed name: the number itself when rational, `αk`
    /// otherwise.
    fn root_name(&self, index: usize) -> String {
        match &self.roots[index] {
            SamplePoint::Rational(value) => format_rational(value),
            SamplePoint::Algebraic { .. } => format!("α{}", index + 1),
        }
    }
}

/// The quantifier-free formula the elimination produces, with the projection it
/// came from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FormulaCertificate {
    /// The cell decomposition and its certificate.
    pub projection: ProjectionCertificate,
    /// The merged intervals, ascending and pairwise separated.
    pub intervals: Vec<XInterval>,
}

impl FormulaCertificate {
    /// Re-derive the cell list, then check the merge.
    ///
    /// After [`ProjectionCertificate::verify`] has re-derived every cell and
    /// every verdict, four independent guards check the intervals:
    ///
    /// 1. every finite endpoint is one of the recomputed cut points
    ///    ([`Fault::IntervalEndpointNotARoot`]);
    /// 2. the intervals ascend and do not overlap
    ///    ([`Fault::IntervalOrderViolation`]);
    /// 3. the cells they cover are **exactly** the true cells
    ///    ([`Fault::IntervalCoverageMismatch`]) — this is the guard a merged
    ///    interval that swallows a false cell runs into;
    /// 4. no two consecutive intervals are contiguous, so the merge is maximal
    ///    ([`Fault::IntervalsNotMerged`]).
    ///
    /// # Errors
    ///
    /// The [`Fault`] naming the guard that rejected.
    pub fn verify(&self) -> Result<(), Fault> {
        self.projection.verify()?;
        let ranges = self.cell_ranges()?;
        check_ranges_ascend(&ranges)?;
        check_coverage(&ranges, &self.projection)?;
        check_merged(&ranges)
    }

    /// The interval list as cell-index ranges, matching every endpoint to a
    /// recomputed cut point.
    fn cell_ranges(&self) -> Result<Vec<(usize, usize)>, Fault> {
        let roots = &self.projection.roots;
        let mut ranges = Vec::with_capacity(self.intervals.len());
        for (index, interval) in self.intervals.iter().enumerate() {
            let start = match &interval.lower {
                None => 0,
                Some(point) => {
                    let k = root_index(roots, point)
                        .ok_or(Fault::IntervalEndpointNotARoot { interval: index })?;
                    if interval.lower_closed {
                        2 * k + 1
                    } else {
                        2 * k + 2
                    }
                }
            };
            let end = match &interval.upper {
                None => 2 * roots.len(),
                Some(point) => {
                    let k = root_index(roots, point)
                        .ok_or(Fault::IntervalEndpointNotARoot { interval: index })?;
                    if interval.upper_closed {
                        2 * k + 1
                    } else {
                        2 * k
                    }
                }
            };
            if start > end || end >= self.projection.cells.len() {
                return Err(Fault::IntervalOrderViolation { interval: index });
            }
            ranges.push((start, end));
        }
        Ok(ranges)
    }

    /// The description string; see [`ProjectionCertificate::describe`].
    #[must_use]
    pub fn describe(&self) -> String {
        self.projection.describe()
    }

    /// The legend; see [`ProjectionCertificate::legend`].
    #[must_use]
    pub fn legend(&self) -> Vec<String> {
        self.projection.legend()
    }
}

/// The ranges are strictly ascending and pairwise disjoint.
fn check_ranges_ascend(ranges: &[(usize, usize)]) -> Result<(), Fault> {
    for index in 1..ranges.len() {
        if ranges[index].0 <= ranges[index - 1].1 {
            return Err(Fault::IntervalOrderViolation { interval: index });
        }
    }
    Ok(())
}

/// The covered cells are exactly the true ones.
fn check_coverage(
    ranges: &[(usize, usize)],
    projection: &ProjectionCertificate,
) -> Result<(), Fault> {
    let mut covered = vec![false; projection.cells.len()];
    for (start, end) in ranges {
        for flag in &mut covered[*start..=*end] {
            *flag = true;
        }
    }
    for (cell, entry) in projection.cells.iter().enumerate() {
        if covered[cell] != entry.verdict {
            return Err(Fault::IntervalCoverageMismatch {
                cell,
                covered: covered[cell],
                verdict: entry.verdict,
            });
        }
    }
    Ok(())
}

/// No two consecutive intervals are contiguous, so the merge was maximal.
fn check_merged(ranges: &[(usize, usize)]) -> Result<(), Fault> {
    for index in 1..ranges.len() {
        if ranges[index].0 == ranges[index - 1].1 + 1 {
            return Err(Fault::IntervalsNotMerged { interval: index });
        }
    }
    Ok(())
}

/// The position of `point` in the cut-point list, by exact structural equality.
fn root_index(roots: &[SamplePoint], point: &SamplePoint) -> Option<usize> {
    roots.iter().position(|root| root == point)
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
    let cut = projection_cut(&projection);
    let isolated = isolate_cut(&cut)?;
    let roots: Vec<SamplePoint> = isolated
        .iter()
        .map(|root| SamplePoint::from_isolated(&cut, root))
        .collect();
    let open_samples = open_cell_samples(&cut, &isolated).map_err(Fault::Declined)?;

    let cells = 2 * roots.len() + 1;
    let mut entries: Vec<CellCertificate> = Vec::with_capacity(cells);
    for cell in 0..cells {
        let sample = if cell.is_multiple_of(2) {
            SamplePoint::Rational(open_samples[cell / 2].clone())
        } else {
            roots[cell / 2].clone()
        };
        entries.push(decide_cell(&formula.atoms, cell, sample)?);
    }
    Ok(ProjectionCertificate {
        atoms: formula.atoms.clone(),
        projection,
        cut,
        roots,
        cells: entries,
    })
}

/// Eliminate `y` and merge the true cells into a quantifier-free formula.
///
/// # Errors
///
/// The [`Fault`] that stopped [`eliminate_y`].
pub fn eliminate_y_to_formula(formula: &ExistsYFormula) -> Result<FormulaCertificate, Fault> {
    let projection = eliminate_y(formula)?;
    let intervals = projection.intervals();
    Ok(FormulaCertificate {
        projection,
        intervals,
    })
}

/// Decide one cell's fibre, by the ℚ route at a rational sample and the `ℚ(α)`
/// route at an algebraic one.
fn decide_cell(
    atoms: &[BiAtom],
    cell: usize,
    sample: SamplePoint,
) -> Result<CellCertificate, Fault> {
    match &sample {
        SamplePoint::Rational(x) => {
            let substituted = substitute_atoms(atoms, x);
            let decision = decide_exists(&ExistsFormula::new(substituted));
            let verdict = decision
                .verify()
                .map_err(|fault| Fault::Univariate { cell, fault })?
                .ok_or_else(|| {
                    Fault::Declined(format!("the fibre over cell {cell} could not be decided"))
                })?;
            Ok(CellCertificate {
                sample,
                verdict,
                fibre: CellFibre::Rational(decision),
            })
        }
        SamplePoint::Algebraic {
            defining_poly,
            lower,
            upper,
        } => {
            let certificate =
                fibre::decide_fibre(defining_poly, lower, upper, &substitution_atoms(atoms))
                    .map_err(|fault| Fault::Fibre { cell, fault })?;
            let verdict = certificate.verdict();
            Ok(CellCertificate {
                sample,
                verdict,
                fibre: CellFibre::Algebraic(Box::new(certificate)),
            })
        }
    }
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
    let mut positive_degree: Vec<BiPoly> = Vec::new();
    for atom in atoms {
        for reductum in reducta(&atom.poly) {
            match degree_y(&reductum) {
                None => {}
                Some(0) => insert_projection(&mut set, &reductum[0]),
                Some(k) => {
                    insert_projection(&mut set, &reductum[k]);
                    if k >= 2 {
                        add_discriminant(&mut set, &reductum)?;
                    }
                    positive_degree.push(reductum);
                }
            }
        }
    }
    add_pairwise_resultants(&mut set, positive_degree)?;
    Ok(set.into_values().collect())
}

/// The same projection operator applied to a bare list of polynomials rather
/// than to atoms — the entry point [`crate::qe::lift`] uses for its second
/// level, where the input is a projection set and not a formula.
///
/// The relation carried by each [`BiAtom`] is immaterial to
/// [`projection_set`], which reads only the polynomials; building the atoms
/// here rather than at the caller keeps that fact inside the module that owns
/// it.
///
/// # Errors
///
/// The [`Fault`] [`projection_set`] raises.
pub(super) fn projection_set_of_polys(polys: &[BiPoly]) -> Result<Vec<Vec<Rational>>, Fault> {
    let atoms: Vec<BiAtom> = polys
        .iter()
        .map(|poly| BiAtom::new(poly.clone(), Relation::Eq))
        .collect();
    projection_set(&atoms)
}

/// Insert a candidate cut polynomial, monic, dropping constants.
fn insert_projection(set: &mut BTreeMap<Vec<(i128, i128)>, Vec<Rational>>, candidate: &[Rational]) {
    if let Some(monic) = canonical(candidate) {
        set.insert(projection_key(&monic), monic);
    }
}

/// The discriminant of one reductum, falling back to its `y`-square-free part
/// when the plain discriminant vanishes identically.
fn add_discriminant(
    set: &mut BTreeMap<Vec<(i128, i128)>, Vec<Rational>>,
    reductum: &BiPoly,
) -> Result<(), Fault> {
    let derivative = derivative_y(reductum)
        .ok_or_else(|| Fault::Declined("the y-derivative overflowed i128".to_string()))?;
    let discriminant = resultant_y(reductum, &derivative)
        .ok_or_else(|| Fault::Declined("a discriminant resultant overflowed i128".to_string()))?;
    if poly::rat_degree(&discriminant).is_some() {
        insert_projection(set, &discriminant);
        return Ok(());
    }
    // The reductum has a repeated `y`-factor. Its distinct branches collide
    // exactly where the discriminant of its square-free part vanishes.
    let squarefree = y_squarefree_part(reductum).ok_or_else(|| {
        Fault::Declined("the y-square-free part could not be formed exactly".to_string())
    })?;
    match degree_y(&squarefree) {
        None => Err(Fault::DegenerateProjection {
            what: "an atom's y-square-free part is the zero polynomial",
        }),
        // One branch cannot collide with itself, so nothing is needed.
        Some(0 | 1) => Ok(()),
        Some(_) => {
            let derivative = derivative_y(&squarefree).ok_or_else(|| {
                Fault::Declined("the square-free y-derivative overflowed i128".to_string())
            })?;
            let discriminant = resultant_y(&squarefree, &derivative).ok_or_else(|| {
                Fault::Declined("a square-free discriminant overflowed i128".to_string())
            })?;
            if poly::rat_degree(&discriminant).is_none() {
                return Err(Fault::DegenerateProjection {
                    what: "the discriminant of an atom's square-free part still vanishes",
                });
            }
            insert_projection(set, &discriminant);
            Ok(())
        }
    }
}

/// Pairwise resultants across distinct reducta. Duplicates are dropped first:
/// `res_y(p, p)` is identically zero and carries nothing.
fn add_pairwise_resultants(
    set: &mut BTreeMap<Vec<(i128, i128)>, Vec<Rational>>,
    positive_degree: Vec<BiPoly>,
) -> Result<(), Fault> {
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
            insert_projection(set, &resultant);
        }
    }
    Ok(())
}

// ============================================================================
// The `y`-square-free part, by pseudo-division over ℚ[x].
// ============================================================================

/// The `BigRational` view of a bivariate polynomial.
fn big_bipoly(p: &BiPoly) -> BigBiPoly {
    p.iter().map(|c| big_poly(c)).collect()
}

/// Back to the `i128` surface, or `None` if a coefficient does not fit.
pub(super) fn bipoly_of_big(p: &BigBiPoly) -> Option<BiPoly> {
    p.iter()
        .map(|c| c.iter().map(rational_of_big).collect::<Option<Vec<_>>>())
        .collect()
}

/// The `y`-degree of a `BigBiPoly`.
fn bi_degree_y(p: &BigBiPoly) -> Option<usize> {
    p.iter().rposition(|c| big::degree(c).is_some())
}

/// `a + b` in `ℚ[x]`.
fn add_x(a: &[BigRational], b: &[BigRational]) -> Vec<BigRational> {
    let mut out = vec![BigRational::zero(); a.len().max(b.len())];
    for (index, coeff) in a.iter().enumerate() {
        out[index] += coeff;
    }
    for (index, coeff) in b.iter().enumerate() {
        out[index] += coeff;
    }
    big::trim(out)
}

/// `−a` in `ℚ[x]`.
fn neg_x(a: &[BigRational]) -> Vec<BigRational> {
    a.iter().map(core::ops::Neg::neg).collect()
}

/// `a + b`, coefficient by coefficient in `ℚ[x]`.
pub(super) fn bi_add(a: &BigBiPoly, b: &BigBiPoly) -> BigBiPoly {
    let mut out = vec![Vec::new(); a.len().max(b.len())];
    for (index, coeff) in a.iter().enumerate() {
        out[index] = add_x(&out[index], coeff);
    }
    for (index, coeff) in b.iter().enumerate() {
        out[index] = add_x(&out[index], coeff);
    }
    out
}

/// `a − b`.
pub(super) fn bi_sub(a: &BigBiPoly, b: &BigBiPoly) -> BigBiPoly {
    bi_add(a, &b.iter().map(|c| neg_x(c)).collect::<BigBiPoly>())
}

/// `a · c` for a `c ∈ ℚ[x]`.
pub(super) fn bi_scale(a: &BigBiPoly, c: &[BigRational]) -> BigBiPoly {
    a.iter().map(|coeff| big::mul(coeff, c)).collect()
}

/// `a · yᵏ`.
pub(super) fn bi_shift(a: &BigBiPoly, k: usize) -> BigBiPoly {
    let mut out = vec![Vec::new(); k];
    out.extend(a.iter().cloned());
    out
}

/// `∂a/∂y`.
fn bi_derivative_y(a: &BigBiPoly) -> BigBiPoly {
    a.iter()
        .enumerate()
        .skip(1)
        .map(|(k, c)| {
            let scale = BigRational::from_integer(BigInt::from(k));
            c.iter().map(|coeff| coeff * &scale).collect()
        })
        .collect()
}

/// Pseudo-division: `lc(b)ᵏ · a = q · b + r` with `deg_y r < deg_y b`, for some
/// `k`. Only ring operations in `ℚ[x]` are used, so no coefficient inverse is
/// ever needed and nothing overflows.
fn bi_pdivmod(a: &BigBiPoly, b: &BigBiPoly) -> Option<(BigBiPoly, BigBiPoly)> {
    let b_degree = bi_degree_y(b)?;
    let leading = b[b_degree].clone();
    let mut remainder = a.clone();
    let mut quotient: BigBiPoly = Vec::new();
    let mut steps = 0usize;
    while let Some(r_degree) = bi_degree_y(&remainder) {
        if r_degree < b_degree {
            break;
        }
        steps += 1;
        if steps > MAX_PSEUDO_STEPS {
            return None;
        }
        let factor = remainder[r_degree].clone();
        let shift = r_degree - b_degree;
        quotient = bi_add(
            &bi_scale(&quotient, &leading),
            &bi_shift(&vec![factor.clone()], shift),
        );
        remainder = bi_sub(
            &bi_scale(&remainder, &leading),
            &bi_shift(&bi_scale(b, &factor), shift),
        );
    }
    Some((quotient, remainder))
}

/// `gcd_y(a, b)` over `ℚ(x)`, up to a factor in `ℚ[x]`, by a pseudo-remainder
/// sequence.
fn bi_pgcd(a: &BigBiPoly, b: &BigBiPoly) -> Option<BigBiPoly> {
    let mut left = a.clone();
    let mut right = b.clone();
    let mut steps = 0usize;
    while bi_degree_y(&right).is_some() {
        steps += 1;
        if steps > MAX_PSEUDO_STEPS {
            return None;
        }
        let (_, remainder) = bi_pdivmod(&left, &right)?;
        left = right;
        right = remainder;
    }
    Some(left)
}

/// The `y`-square-free part of `p`, up to a nonzero factor in `ℚ[x]`.
///
/// `p / gcd_y(p, ∂p/∂y)`, computed by pseudo-division so that no coefficient
/// inverse in `ℚ(x)` is needed. `None` when the division is not exact or when a
/// coefficient of the result does not fit `i128`, in which case the caller
/// declines rather than guessing.
fn y_squarefree_part(p: &BiPoly) -> Option<BiPoly> {
    let lifted = big_bipoly(p);
    let degree = bi_degree_y(&lifted)?;
    if degree <= 1 {
        return Some(p.clone());
    }
    let derivative = bi_derivative_y(&lifted);
    let common = bi_pgcd(&lifted, &derivative)?;
    if bi_degree_y(&common)? == 0 {
        return Some(p.clone());
    }
    let (quotient, remainder) = bi_pdivmod(&lifted, &common)?;
    if bi_degree_y(&remainder).is_some() {
        return None;
    }
    bipoly_of_big(&quotient)
}

// ============================================================================
// Cut points and cell samples.
// ============================================================================

/// The **cut polynomial**: the square-free part of the projection set's
/// product. Empty when the projection set cuts nothing.
pub(super) fn projection_cut(projection: &[Vec<Rational>]) -> Vec<BigRational> {
    let mut product = vec![BigRational::one()];
    for candidate in projection {
        product = big::mul(&product, &big_poly(candidate));
    }
    if big::degree(&product).is_none_or(|d| d == 0) {
        return Vec::new();
    }
    big::squarefree_part(&product).unwrap_or_default()
}

/// The isolated distinct real roots of the cut polynomial, ascending.
///
/// # Errors
///
/// [`Fault::Declined`] when the bisection budget runs out.
pub(super) fn isolate_cut(cut: &[BigRational]) -> Result<Vec<big::IsolatedRoot>, Fault> {
    if big::degree(cut).is_none_or(|d| d == 0) {
        return Ok(Vec::new());
    }
    big::isolate(cut).ok_or_else(|| {
        Fault::Declined("root isolation ran out of its bisection budget".to_string())
    })
}

/// The cut points as sample points: rational when recognised, an isolating
/// bracket otherwise.
pub(super) fn cut_points(cut: &[BigRational]) -> Result<Vec<SamplePoint>, Fault> {
    Ok(isolate_cut(cut)?
        .iter()
        .map(|root| SamplePoint::from_isolated(cut, root))
        .collect())
}

/// The recorded sample of cell `cell` really lies in that cell.
pub(super) fn check_sample_in_cell(
    roots: &[SamplePoint],
    cell: usize,
    sample: &SamplePoint,
) -> Result<(), Fault> {
    if cell.is_multiple_of(2) {
        let SamplePoint::Rational(value) = sample else {
            return Err(Fault::CellSampleOutOfOrder { cell });
        };
        let k = cell / 2;
        let above_previous = k == 0 || root_is_below(&roots[k - 1], value)?;
        let below_next = k == roots.len() || root_is_above(&roots[k], value)?;
        if above_previous && below_next {
            return Ok(());
        }
    } else if roots.get(cell / 2) == Some(sample) {
        return Ok(());
    }
    Err(Fault::CellSampleOutOfOrder { cell })
}

/// The cut point is strictly below the rational.
fn root_is_below(root: &SamplePoint, value: &BigRational) -> Result<bool, Fault> {
    let ordering = compare_sample_to_rational(root, value)
        .ok_or_else(|| Fault::Declined("a cut-point comparison declined".to_string()))?;
    Ok(ordering == core::cmp::Ordering::Less)
}

/// The cut point is strictly above the rational.
fn root_is_above(root: &SamplePoint, value: &BigRational) -> Result<bool, Fault> {
    let ordering = compare_sample_to_rational(root, value)
        .ok_or_else(|| Fault::Declined("a cut-point comparison declined".to_string()))?;
    Ok(ordering == core::cmp::Ordering::Greater)
}

/// `divisor` divides `dividend` exactly over ℚ, and is not a constant.
pub(super) fn divides(divisor: &[BigRational], dividend: &[BigRational]) -> bool {
    if big::degree(divisor).is_none_or(|d| d == 0) {
        return false;
    }
    big::rem(dividend, divisor).is_some_and(|r| big::degree(&r).is_none())
}

// ============================================================================
// Substitution.
// ============================================================================

/// `pᵢ(x₀, y)` for every atom at a **rational** `x₀`.
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

/// The atoms as the `ℚ(α)` fibre engine wants them.
fn substitution_atoms(atoms: &[BiAtom]) -> Vec<fibre::SubstitutionAtom> {
    atoms
        .iter()
        .map(|atom| fibre::SubstitutionAtom {
            coefficients: atom.poly.iter().map(|c| big_poly(c)).collect(),
            relation: atom.relation,
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

/// A polynomial as `c0 + c1*x + …`, terms with zero coefficients omitted.
fn format_poly(p: &[BigRational]) -> String {
    let mut terms: Vec<String> = Vec::new();
    for (power, coefficient) in p.iter().enumerate() {
        if coefficient.is_zero() {
            continue;
        }
        let value = format_rational(coefficient);
        terms.push(match power {
            0 => value,
            1 => format!("{value}*x"),
            _ => format!("{value}*x^{power}"),
        });
    }
    if terms.is_empty() {
        return "0".to_string();
    }
    terms.join(" + ")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(n: i128) -> Rational {
        Rational::integer(n)
    }

    fn q(n: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(n))
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

    fn formula(atoms: Vec<BiAtom>) -> FormulaCertificate {
        let certificate = eliminate_y_to_formula(&ExistsYFormula::new(atoms))
            .expect("the projection must succeed");
        certificate.verify().expect("the certificate must verify");
        certificate
    }

    fn verdicts(certificate: &ProjectionCertificate) -> Vec<bool> {
        certificate.cells.iter().map(|c| c.verdict).collect()
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
            verdicts(&certificate),
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
        assert_eq!(
            certificate.roots,
            vec![SamplePoint::Rational(BigRational::zero())]
        );
    }

    #[test]
    fn a_total_degree_four_atom_with_a_vanishing_leading_coefficient_is_true_everywhere() {
        // ∃y. x²y² − 1 < 0 ∧ y > 0.  For x ≠ 0 the condition is 0 < y < 1/|x|;
        // at x = 0 the first atom is the constant −1 and every y works. So the
        // answer is the whole line — but only because the projection notices
        // that the leading `y`-coefficient x² vanishes at 0 and gives that
        // point its own cell.
        let certificate = decided(vec![
            atom(&[&[-1], &[0], &[0, 0, 1]], Relation::Lt),
            atom(&[&[0], &[1]], Relation::Gt),
        ]);
        assert_eq!(certificate.describe(), "x ∈ (-∞, ∞)");
        assert_eq!(
            certificate.roots,
            vec![SamplePoint::Rational(BigRational::zero())]
        );
        assert_eq!(certificate.cells.len(), 3);
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

    // ------------------------------------------------ irrational boundaries

    #[test]
    fn the_circle_of_radius_root_two_with_y_positive_has_two_algebraic_endpoints() {
        // ∃y. x² + y² − 2 = 0 ∧ y > 0  →  −√2 < x < √2.
        let certificate = decided(vec![
            atom(&[&[-2, 0, 1], &[0], &[1]], Relation::Eq),
            atom(&[&[0], &[1]], Relation::Gt),
        ]);
        assert_eq!(certificate.describe(), "x ∈ (α1, α2)");
        assert_eq!(certificate.roots.len(), 2);
        assert!(
            certificate
                .roots
                .iter()
                .all(|root| matches!(root, SamplePoint::Algebraic { .. })),
            "both cut points are ±√2, neither rational"
        );
        assert_eq!(
            verdicts(&certificate),
            vec![false, false, true, false, false],
            "the point cells at ±√2 are false: there y = 0 and `y > 0` fails"
        );
        let legend = certificate.legend();
        assert_eq!(legend.len(), 2);
        assert!(
            legend[0].contains("-2 + 1*x^2"),
            "α1's defining polynomial is x² − 2, got {legend:?}"
        );
    }

    #[test]
    fn the_point_cell_at_root_two_is_decided_in_q_root_two_with_a_repeated_fibre_root() {
        // At x = √2 the fibre is y² + (α² − 2) = y², whose only root is the
        // *double* root y = 0. The K-decomposition must still produce exactly
        // one cut point there, and the sign of `y` at it must be computed in K.
        let certificate = decided(vec![
            atom(&[&[-2, 0, 1], &[0], &[1]], Relation::Eq),
            atom(&[&[0], &[1]], Relation::Gt),
        ]);
        let CellFibre::Algebraic(fibre_certificate) = &certificate.cells[3].fibre else {
            panic!("cell 3 is the point cell at √2 and must use the ℚ(α) route");
        };
        assert_eq!(
            fibre_certificate.modulus,
            vec![q(-2), q(0), q(1)],
            "the modulus split down to x² − 2"
        );
        // x² − 2 substituted at α is the *zero element* of K.
        assert_eq!(fibre_certificate.atoms[0].poly[0], fibre::Element::new());
        let fibre::FibreDecision::False(refutation) = &fibre_certificate.decision else {
            panic!("y > 0 fails in the fibre over √2");
        };
        assert_eq!(
            refutation.roots,
            vec![fibre::FieldSample::Rational(BigRational::zero())],
            "y² has the single distinct root 0"
        );
        assert_eq!(refutation.failures.len(), 3);
        assert_eq!(
            refutation.failures[1].sign, 0,
            "at y = 0 the sign of `y` computed in K is zero, which is why `y > 0` fails"
        );
        assert!(!fibre_certificate.verify().expect("the fibre verifies"));
    }

    #[test]
    fn the_parabola_meeting_the_hyperbola_is_the_single_rational_point_one() {
        // ∃y. y² = x ∧ x·y = 1.  Both cut points come out rational (0 and 1),
        // so this exercises the ℚ route with the same front door.
        let certificate = decided(vec![
            atom(&[&[0, -1], &[0], &[1]], Relation::Eq),
            atom(&[&[-1], &[0, 1]], Relation::Eq),
        ]);
        assert_eq!(certificate.describe(), "x ∈ {1}");
        assert!(
            certificate
                .roots
                .iter()
                .all(|root| matches!(root, SamplePoint::Rational(_)))
        );
    }

    #[test]
    fn the_fibre_over_the_cube_root_of_two_has_a_y_algebraic_over_the_field() {
        // ∃y. y² = x ∧ x³ = 2 — true exactly at x = ∛2, where y = ±2^{1/6} is
        // algebraic **over** K = ℚ(∛2), not an element of it. The fibre's
        // sample therefore has to be carried as a polynomial over K plus a
        // bracket; there is no element of K to name it with.
        let certificate = decided(vec![
            atom(&[&[0, -1], &[0], &[1]], Relation::Eq),
            atom(&[&[-2, 0, 0, 1]], Relation::Eq),
        ]);
        assert_eq!(certificate.describe(), "x ∈ {α2}");
        assert_eq!(certificate.roots.len(), 2, "the cut points are 0 and ∛2");
        let CellFibre::Algebraic(fibre_certificate) = &certificate.cells[3].fibre else {
            panic!("cell 3 is the point cell at ∛2");
        };
        assert_eq!(fibre_certificate.modulus, vec![q(-2), q(0), q(0), q(1)]);
        let fibre::FibreDecision::True(witness) = &fibre_certificate.decision else {
            panic!("y² = ∛2 is solvable");
        };
        assert!(
            matches!(witness.sample, fibre::FieldSample::Algebraic { .. }),
            "the witnessing y is algebraic over K, not a rational"
        );
    }

    #[test]
    fn a_squared_atom_with_a_cube_root_boundary_is_true_exactly_at_the_cube_root() {
        // ∃y. (y − x)² ≤ 0 ∧ x³ − 2 = 0 — true exactly at x = ∛2, a point cell
        // over ℚ(∛2). The first atom's own discriminant vanishes identically,
        // so this also exercises the square-free fallback in the projection.
        let certificate = decided(vec![
            atom(&[&[0, 0, 1], &[0, -2], &[1]], Relation::Le),
            atom(&[&[-2, 0, 0, 1]], Relation::Eq),
        ]);
        assert_eq!(certificate.describe(), "x ∈ {α2}");
        assert_eq!(certificate.roots.len(), 2, "the cut points are 0 and ∛2");
        let CellFibre::Algebraic(fibre_certificate) = &certificate.cells[3].fibre else {
            panic!("cell 3 is the point cell at ∛2");
        };
        assert_eq!(
            fibre_certificate.modulus,
            vec![q(-2), q(0), q(0), q(1)],
            "the modulus split down to x³ − 2"
        );
        assert!(fibre_certificate.verify().expect("the fibre verifies"));
    }

    #[test]
    fn the_y_square_free_part_of_a_perfect_square_drops_to_degree_one() {
        // (y − x)² has y-degree 2 but describes one branch.
        let squared = bipoly(&[&[0, 0, 1], &[0, -2], &[1]]);
        let squarefree = y_squarefree_part(&squared).expect("the square-free part exists");
        assert_eq!(degree_y(&squarefree), Some(1));
        // The positive control: a genuinely square-free atom is returned as is.
        let distinct = bipoly(&[&[0, -1], &[0], &[1]]);
        assert_eq!(y_squarefree_part(&distinct), Some(distinct));
    }

    // -------------------------------------------------------- the formula

    #[test]
    fn the_formula_merges_the_point_cell_into_the_half_line() {
        // ∃y. y² − x = 0: cells {0} and (0, ∞) are both true and merge into
        // one interval [0, ∞).
        let certificate = formula(vec![atom(&[&[0, -1], &[0], &[1]], Relation::Eq)]);
        assert_eq!(certificate.intervals.len(), 1);
        assert_eq!(
            certificate.intervals[0],
            XInterval {
                lower: Some(SamplePoint::Rational(BigRational::zero())),
                lower_closed: true,
                upper: None,
                upper_closed: false,
            }
        );
        assert_eq!(certificate.describe(), "x ∈ [0, ∞)");
    }

    #[test]
    fn the_formula_endpoints_of_the_root_two_circle_are_the_algebraic_cut_points() {
        let certificate = formula(vec![
            atom(&[&[-2, 0, 1], &[0], &[1]], Relation::Eq),
            atom(&[&[0], &[1]], Relation::Gt),
        ]);
        assert_eq!(certificate.intervals.len(), 1);
        let interval = &certificate.intervals[0];
        assert_eq!(
            interval.lower.as_ref(),
            certificate.projection.roots.first()
        );
        assert_eq!(interval.upper.as_ref(), certificate.projection.roots.get(1));
        assert!(!interval.lower_closed && !interval.upper_closed);
        assert_eq!(certificate.describe(), "x ∈ (α1, α2)");
    }

    #[test]
    fn a_formula_with_no_true_cell_has_no_intervals() {
        // ∃y. y² + 1 = 0 — never.
        let certificate = formula(vec![atom(&[&[1], &[0], &[1]], Relation::Eq)]);
        assert!(certificate.intervals.is_empty());
        assert_eq!(certificate.describe(), "∅");
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
    fn a_certificate_with_a_tampered_cut_polynomial_is_refused() {
        let mut certificate = decided(vec![atom(&[&[-1, 0, 1], &[0], &[1]], Relation::Lt)]);
        certificate.cut.push(q(1));
        assert!(matches!(
            certificate.verify(),
            Err(Fault::CutMismatch { .. })
        ));
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
        certificate.cells[0].sample = SamplePoint::Rational(q(5));
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
        let borrowed = certificate.cells[2].fibre.clone();
        certificate.cells[0].fibre = borrowed;
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
        let CellFibre::Rational(Decision::True(cert)) = &mut certificate.cells[2].fibre else {
            panic!("cell 2 is the satisfying one");
        };
        cert.signs[0] = -cert.signs[0];
        assert!(matches!(
            certificate.verify(),
            Err(Fault::Univariate { cell: 2, .. })
        ));
    }

    #[test]
    fn a_sign_at_alpha_claimed_wrong_is_refused_by_the_fibre_checker() {
        let mut certificate = decided(vec![
            atom(&[&[0, 0, 1], &[0, -2], &[1]], Relation::Le),
            atom(&[&[-2, 0, 0, 1]], Relation::Eq),
        ]);
        let CellFibre::Algebraic(fibre_certificate) = &mut certificate.cells[3].fibre else {
            panic!("cell 3 is the point cell at ∛2");
        };
        let fibre::FibreDecision::True(witness) = &mut fibre_certificate.decision else {
            panic!("the fibre over ∛2 is satisfiable");
        };
        witness.signs[0] = 1; // it is really 0: (y − α)² vanishes at y = α
        assert!(matches!(
            certificate.verify(),
            Err(Fault::Fibre {
                cell: 3,
                fault: fibre::Fault::SignMismatch { index: 0, .. }
            })
        ));
    }

    #[test]
    fn a_fibre_modulus_that_does_not_divide_the_cut_polynomial_is_refused() {
        let mut certificate = decided(vec![
            atom(&[&[-2, 0, 1], &[0], &[1]], Relation::Eq),
            atom(&[&[0], &[1]], Relation::Gt),
        ]);
        let CellFibre::Algebraic(fibre_certificate) = &mut certificate.cells[3].fibre else {
            panic!("cell 3 is the point cell at √2");
        };
        // x² − 3 has a root in (1, 2] too, but does not divide the cut.
        fibre_certificate.modulus = vec![q(-3), q(0), q(1)];
        assert_eq!(
            certificate.verify(),
            Err(Fault::ModulusNotADivisor { cell: 3 })
        );
    }

    #[test]
    fn a_fibre_certificate_about_a_different_bracket_is_refused() {
        let mut certificate = decided(vec![
            atom(&[&[-2, 0, 1], &[0], &[1]], Relation::Eq),
            atom(&[&[0], &[1]], Relation::Gt),
        ]);
        let CellFibre::Algebraic(fibre_certificate) = &mut certificate.cells[3].fibre else {
            panic!("cell 3 is the point cell at √2");
        };
        fibre_certificate.lower = q(-100);
        assert_eq!(
            certificate.verify(),
            Err(Fault::FibreBracketMismatch { cell: 3 })
        );
    }

    #[test]
    fn an_algebraic_cell_whose_substituted_atoms_were_tampered_with_is_refused() {
        let mut certificate = decided(vec![
            atom(&[&[-2, 0, 1], &[0], &[1]], Relation::Eq),
            atom(&[&[0], &[1]], Relation::Gt),
        ]);
        let CellFibre::Algebraic(fibre_certificate) = &mut certificate.cells[3].fibre else {
            panic!("cell 3 is the point cell at √2");
        };
        // Claim the fibre is `y² + 1 = 0` where the substitution gives `y² = 0`.
        fibre_certificate.atoms[0].poly[0] = vec![q(1)];
        assert_eq!(
            certificate.verify(),
            Err(Fault::SubstitutionMismatch { cell: 3 })
        );
    }

    #[test]
    fn a_fibre_refutation_that_drops_a_y_root_is_refused_as_an_incomplete_root_list() {
        let mut certificate = decided(vec![
            atom(&[&[-2, 0, 1], &[0], &[1]], Relation::Eq),
            atom(&[&[0], &[1]], Relation::Gt),
        ]);
        let CellFibre::Algebraic(fibre_certificate) = &mut certificate.cells[3].fibre else {
            panic!("cell 3 is the point cell at √2");
        };
        let fibre::FibreDecision::False(refutation) = &mut fibre_certificate.decision else {
            panic!("the fibre over √2 is unsatisfiable");
        };
        assert_eq!(refutation.roots.len(), 1, "the only y-root is 0");
        // Drop it, keeping every count self-consistent so the counting guards
        // do not fire first: one cell, one open sample, no roots.
        refutation.roots.clear();
        refutation.open_samples.truncate(1);
        refutation.failures.truncate(1);
        assert!(matches!(
            certificate.verify(),
            Err(Fault::Fibre {
                cell: 3,
                fault: fibre::Fault::IncompleteRootList { .. }
            })
        ));
    }

    #[test]
    fn a_fibre_cell_nominating_a_conjunct_that_holds_is_refused() {
        let mut certificate = decided(vec![
            atom(&[&[-2, 0, 1], &[0], &[1]], Relation::Eq),
            atom(&[&[0], &[1]], Relation::Gt),
        ]);
        let CellFibre::Algebraic(fibre_certificate) = &mut certificate.cells[3].fibre else {
            panic!("cell 3 is the point cell at √2");
        };
        let fibre::FibreDecision::False(refutation) = &mut fibre_certificate.decision else {
            panic!("the fibre over √2 is unsatisfiable");
        };
        // In the y-cell {0} it is `y > 0` that fails, not `y² = 0`.
        refutation.failures[1] = fibre::FibreCellFailure {
            conjunct: 0,
            sign: 0,
        };
        assert!(matches!(
            certificate.verify(),
            Err(Fault::Fibre {
                cell: 3,
                fault: fibre::Fault::ConjunctDoesNotFail {
                    cell: 1,
                    index: 0,
                    sign: 0
                }
            })
        ));
    }

    #[test]
    fn a_fibre_witness_whose_bracket_holds_two_roots_is_refused() {
        // The fibre over ∛2 is `y² = ∛2`, whose two real roots are ±2^{1/6};
        // widening the witness bracket to hold both makes it name nothing.
        let mut certificate = decided(vec![
            atom(&[&[0, -1], &[0], &[1]], Relation::Eq),
            atom(&[&[-2, 0, 0, 1]], Relation::Eq),
        ]);
        let CellFibre::Algebraic(fibre_certificate) = &mut certificate.cells[3].fibre else {
            panic!("cell 3 is the point cell at ∛2");
        };
        let fibre::FibreDecision::True(witness) = &mut fibre_certificate.decision else {
            panic!("y² = ∛2 is solvable");
        };
        let fibre::FieldSample::Algebraic { upper, .. } = &mut witness.sample else {
            panic!("the witnessing y is algebraic over K");
        };
        *upper = q(10);
        assert!(matches!(
            certificate.verify(),
            Err(Fault::Fibre {
                cell: 3,
                fault: fibre::Fault::SampleNotIsolating {
                    roots_in_bracket: 2
                }
            })
        ));
    }

    #[test]
    fn a_rational_cell_carrying_an_algebraic_fibre_is_refused_as_a_kind_mismatch() {
        let mut certificate = decided(vec![
            atom(&[&[-2, 0, 1], &[0], &[1]], Relation::Eq),
            atom(&[&[0], &[1]], Relation::Gt),
        ]);
        let borrowed = certificate.cells[3].fibre.clone();
        certificate.cells[2].fibre = borrowed;
        assert_eq!(
            certificate.verify(),
            Err(Fault::FibreKindMismatch { cell: 2 })
        );
    }

    // -------------------------------------------------- forged formulas

    #[test]
    fn a_merged_interval_that_swallows_a_false_cell_is_refused() {
        let mut certificate = formula(vec![
            atom(&[&[-2, 0, 1], &[0], &[1]], Relation::Eq),
            atom(&[&[0], &[1]], Relation::Gt),
        ]);
        // Widen (α1, α2) to (−∞, α2): cells 0 and 1 are false but now covered.
        certificate.intervals[0].lower = None;
        assert_eq!(
            certificate.verify(),
            Err(Fault::IntervalCoverageMismatch {
                cell: 0,
                covered: true,
                verdict: false
            })
        );
    }

    #[test]
    fn an_interval_endpoint_that_is_not_a_cut_point_is_refused() {
        let mut certificate = formula(vec![atom(&[&[-1, 0, 1], &[0], &[1]], Relation::Lt)]);
        certificate.intervals[0].lower = Some(SamplePoint::Rational(q(7)));
        assert_eq!(
            certificate.verify(),
            Err(Fault::IntervalEndpointNotARoot { interval: 0 })
        );
    }

    #[test]
    fn two_intervals_that_should_have_been_merged_are_refused() {
        // ∃y. y² − x = 0 is true on {0} ∪ (0, ∞); splitting that back into two
        // adjacent intervals is not the merged form.
        let mut certificate = formula(vec![atom(&[&[0, -1], &[0], &[1]], Relation::Eq)]);
        let zero = SamplePoint::Rational(BigRational::zero());
        certificate.intervals = vec![
            XInterval {
                lower: Some(zero.clone()),
                lower_closed: true,
                upper: Some(zero),
                upper_closed: true,
            },
            XInterval {
                lower: certificate.projection.roots.first().cloned(),
                lower_closed: false,
                upper: None,
                upper_closed: false,
            },
        ];
        assert_eq!(
            certificate.verify(),
            Err(Fault::IntervalsNotMerged { interval: 1 })
        );
    }

    #[test]
    fn two_overlapping_intervals_are_refused() {
        let mut certificate = formula(vec![atom(&[&[0, -1], &[0], &[1]], Relation::Eq)]);
        let interval = certificate.intervals[0].clone();
        certificate.intervals.push(interval);
        assert_eq!(
            certificate.verify(),
            Err(Fault::IntervalOrderViolation { interval: 1 })
        );
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
