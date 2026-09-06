//! Real quantifier elimination with sample-point certificates: the univariate
//! fragment, disjunctive normal form under `∃`, and one bivariate projection
//! step.
//!
//! # What is decided
//!
//! Polynomial atoms `p ▷ 0` with `▷ ∈ {=, ≠, <, ≤, >, ≥}` and exact rational
//! coefficients ([`num_rational::BigRational`] — **no** `i128`, so no
//! coefficient is too large).
//!
//! - [`ExistsFormula`] — `∃x. ⋀ᵢ pᵢ(x) ▷ᵢ 0`, decided by [`decide_exists`];
//! - [`ForallFormula`] — `∀x. ⋁ᵢ pᵢ(x) ▷ᵢ 0`, decided by [`decide_forall`]
//!   through the De Morgan dual (the negation table is on
//!   [`Relation::negate`]);
//! - [`dnf::Dnf`] — `∃x. ⋁ᵢ ⋀ⱼ pᵢⱼ(x) ▷ᵢⱼ 0`, decided by
//!   [`dnf::decide_exists_dnf`]. A disjunction is a **first-class object** here,
//!   not a caller's loop: its `true` certificate names the disjunct it
//!   satisfies, and its `false` certificate names, in every cell, a failing
//!   conjunct **for every disjunct**;
//! - [`bivariate::ExistsYFormula`] — `∃y. ⋀ᵢ pᵢ(x, y) ▷ᵢ 0` at total degree at
//!   most [`bivariate::MAX_TOTAL_DEGREE`], eliminated by
//!   [`bivariate::eliminate_y`] into a quantifier-free description of the
//!   `x`-line as a list of cells with a verdict each, or by
//!   [`bivariate::eliminate_y_to_formula`] into the merged union of
//!   `x`-intervals with algebraic endpoints. A cell boundary that is **not**
//!   rational is decided, not declined: [`fibre`] does the fibre arithmetic in
//!   `ℚ(α)`;
//! - [`fibre::decide_fibre`] — `∃y. ⋀ᵢ qᵢ(y) ▷ᵢ 0` with `qᵢ ∈ ℚ(α)[y]` for a
//!   real algebraic `α`, by Sturm chains and real-root isolation over `ℚ(α)`
//!   with every sign settled at `α` exactly;
//! - [`eliminate`] / [`eliminate_forall`] are the thin, self-checking front
//!   doors: they decide and then *verify their own certificate* before
//!   returning a `bool`.
//!
//! The method is the sign-invariant cell decomposition of ℝ. The real roots of
//! every `pᵢ` cut the line into finitely many cells — the roots themselves
//! (point cells) and the open intervals between and beyond them. Inside one
//! cell no `pᵢ` changes sign, so the whole formula has a constant truth value
//! there, and testing one sample per cell decides the sentence. A `true` answer
//! is witnessed by the satisfying sample ([`SampleCertificate`]); a `false`
//! answer is witnessed by the whole decomposition together with, for every
//! cell, a conjunct that fails in it ([`RefutationCertificate`]).
//!
//! # What is **not** decided
//!
//! - **Full CAD.** [`bivariate`] is one projection step in two variables at
//!   bounded degree. There is adjacency along the projected line — adjacent
//!   true cells merge into intervals with algebraic endpoints — but no lifting
//!   to three or more variables and no cell index.
//! - **Quantifier alternation.** `∃x∀y` has no representation here.
//! - **Transcendental atoms** (`sin`, `exp`, …). Atoms are polynomials.
//!
//! # Certificates
//!
//! Every certificate is **data, not a trace**: each carries the formula it
//! speaks about, and its `verify` re-derives every claim from the polynomials
//! alone — it re-isolates roots, recomputes every sign, and re-checks every
//! relation. Nothing produced by the search is trusted. A `verify` failure is
//! reported as a [`Fault`] naming the specific guard that rejected, so a forged
//! certificate is refused with a reason rather than a bare `false`.
//!
//! # Exactness
//!
//! No floating point, and **no `i128`** on the deciding path. Root isolation,
//! Sturm counting, the sign of a polynomial at a rational or at a real
//! algebraic number, and the comparison of an algebraic number with a rational
//! are all `BigRational`, in the private `qe::big` engine. The first slice of this module reused the
//! `i128` machinery in [`crate::sturm`] and [`crate::algebraic`] and therefore
//! declined `∃x. x² − 10³⁰ = 0` — the Sturm chain evaluates near a Cauchy bound
//! of `10³⁰ + 1` and squares it. That decline is gone; `10⁶⁰` decides too. The
//! only remaining declines are named step budgets in the private `qe::big` engine, never an
//! arithmetic wall.
//!
//! The `i128` route is retained under `cfg(test)` and run against the whole
//! first-slice corpus, so "the new engine agrees with the old one wherever the
//! old one had an answer" is a test, not a claim.
//!
//! # What this module reuses
//!
//! - [`axeyum_ir::poly::sylvester_matrix`] and
//!   [`axeyum_ir::poly::sylvester_determinant`] — the bivariate Sylvester
//!   resultant, which is exactly the engine [`crate::resultant`] and
//!   [`crate::discriminant`] call for the univariate case. `crate::resultant`
//!   itself cannot be used for projection: it eliminates a variable from two
//!   *univariate* polynomials and returns a constant, whereas projection needs
//!   `res_y(p, q)` as a polynomial in `x`.
//! - [`crate::sturm`], [`crate::algebraic`] and [`crate::real_algebraic`] — only
//!   in the `cfg(test)` differential route.
//!
//! # Cost profile — ADVISORY
//!
//! Measured 2026-09-05 on a prebuilt `--release` lib-test binary, 20 repeats
//! per shape with process startup subtracted, at load average 8.5 on a shared
//! box. **Single run, advisory only** — do not ratchet on these. Each row is
//! one named test, and the test does more than one decision, so read the row as
//! "the whole shape", not "one call".
//!
//! | shape (the test that is timed) | cost |
//! |---|---|
//! | univariate, cubic, 3 atoms, decide + verify + front door | 0.6 ms |
//! | DNF, 2 disjuncts, 3 atoms, refutation + verify | 0.5 ms |
//! | bivariate, total degree 2 (`x² + y² < 1`), 5 cells + verify | 0.7 ms |
//! | bivariate, total degree 4 (`x²y² − 1 < 0 ∧ y > 0`), 3 cells + verify | 0.7 ms |
//! | univariate, `x² − 10³⁰` (+ the `i128` control) | 14 ms |
//! | univariate, `x² − 10⁶⁰`, two verdicts | 85 ms |
//!
//! The **irrational-boundary** rows were added 2026-09-05 by the same method,
//! 3 repeats of a prebuilt `--release` lib-test binary at load average 14–17 on
//! the same shared box, spread under 10% across repeats. Also advisory.
//!
//! | shape (the test that is timed) | cost |
//! |---|---|
//! | degree 2, irrational boundary (`x² + y² = 2 ∧ y > 0`), two point cells over `ℚ(√2)`, + verify | 42 ms |
//! | degree 4 total (`(y − x)² ≤ 0 ∧ x³ = 2`), one point cell over `ℚ(∛2)`, + verify | 57 ms |
//! | degree 3 field, `y` algebraic **over** `K` (`y² = x ∧ x³ = 2`), + verify | 90 ms |
//!
//! Three things the table says. First, **degree is cheap and magnitude is not**:
//! the bivariate step at degree 4 costs the same as the univariate cubic, while
//! a `10⁶⁰` coefficient costs a hundred times more — isolation bisects from a
//! Cauchy bound of `10⁶⁰`, so it spends ~200 halvings on 60-digit rationals
//! before the rational root is recognised. Second, the bivariate cost is
//! dominated not by the projection but by the `2r + 1` fibre decisions, so it
//! scales with the number of cut points, not with the Sylvester determinants.
//! Third, **an irrational boundary costs about 60× a rational one at the same
//! degree**, and each row above is a producer run *plus* a full independent
//! re-derivation. The multiplier is the `ℚ(α)` layer: every coefficient
//! comparison in a Sturm chain over `K` is a sign at `α` rather than a sign of
//! a rational, and each `K`-remainder needs an inverse modulo the modulus. It
//! is not the number of cells and not the field degree in itself — the `ℚ(∛2)`
//! rows cost 1.4× and 2× the `ℚ(√2)` row while carrying *fewer* algebraic
//! cells, because their fibre polynomials are the ones whose roots are not in
//! `K`.

use core::cmp::Ordering;

use axeyum_ir::Rational;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

#[path = "qe_big.rs"]
pub(crate) mod big;

#[path = "qe_fibre.rs"]
pub mod fibre;

#[path = "qe_bivariate.rs"]
pub mod bivariate;

#[path = "qe_dnf.rs"]
pub mod dnf;

/// How many bisections [`open_cell_samples`] will spend finding a rational
/// strictly between a rational root and the next root along.
const MAX_SEPARATION_STEPS: usize = 4096;

// ============================================================================
// The fragment: atoms and formulas.
// ============================================================================

/// The comparison in an atom `p(x) ▷ 0`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Relation {
    /// `p(x) = 0`
    Eq,
    /// `p(x) ≠ 0`
    Ne,
    /// `p(x) < 0`
    Lt,
    /// `p(x) ≤ 0`
    Le,
    /// `p(x) > 0`
    Gt,
    /// `p(x) ≥ 0`
    Ge,
}

impl Relation {
    /// The logical negation of this relation — the **sign-flip table** that
    /// turns `∀x. ⋁ᵢ pᵢ ▷ᵢ 0` into `¬∃x. ⋀ᵢ pᵢ ▷̄ᵢ 0`:
    ///
    /// | relation | negated |
    /// |---|---|
    /// | `=` | `≠` |
    /// | `≠` | `=` |
    /// | `<` | `≥` |
    /// | `≤` | `>` |
    /// | `>` | `≤` |
    /// | `≥` | `<` |
    ///
    /// Note that the polynomial is untouched: negating the *relation* is
    /// enough, so no atom is ever rewritten and the cell decomposition of the
    /// dual formula is literally the same decomposition.
    #[must_use]
    pub fn negate(self) -> Relation {
        match self {
            Relation::Eq => Relation::Ne,
            Relation::Ne => Relation::Eq,
            Relation::Lt => Relation::Ge,
            Relation::Le => Relation::Gt,
            Relation::Gt => Relation::Le,
            Relation::Ge => Relation::Lt,
        }
    }

    /// Whether `p(x) ▷ 0` holds when `p(x)` has sign `sign` (`-1`, `0`, or
    /// `1`). This is the *only* place a relation is interpreted; both the
    /// producer and every checker call it, which is what makes "the relation
    /// holds at the recomputed sign" a single auditable guard.
    #[must_use]
    pub fn holds(self, sign: i8) -> bool {
        match self {
            Relation::Eq => sign == 0,
            Relation::Ne => sign != 0,
            Relation::Lt => sign < 0,
            Relation::Le => sign <= 0,
            Relation::Gt => sign > 0,
            Relation::Ge => sign >= 0,
        }
    }
}

/// An LSB-first rational polynomial built from integer coefficients — the
/// ergonomic constructor for atoms.
///
/// ```
/// use axeyum_cas::qe::{Atom, ExistsFormula, Relation, eliminate, integer_poly};
///
/// // ∃x. x² − 2 = 0 — true, at an irrational point.
/// let formula = ExistsFormula::new(vec![Atom::new(integer_poly(&[-2, 0, 1]), Relation::Eq)]);
/// assert_eq!(eliminate(&formula), Some(true));
/// ```
#[must_use]
pub fn integer_poly(coefficients: &[i64]) -> Vec<BigRational> {
    coefficients
        .iter()
        .map(|c| BigRational::from_integer(BigInt::from(*c)))
        .collect()
}

/// One atom `poly(x) ▷ 0`, with `poly` LSB-first over ℚ.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Atom {
    /// The polynomial, LSB-first (`poly[k]` is the coefficient of `xᵏ`).
    pub poly: Vec<BigRational>,
    /// The comparison against `0`.
    pub relation: Relation,
}

impl Atom {
    /// Build an atom from an LSB-first coefficient vector and a relation.
    #[must_use]
    pub fn new(poly: Vec<BigRational>, relation: Relation) -> Atom {
        Atom { poly, relation }
    }

    /// The same polynomial with the relation logically negated
    /// ([`Relation::negate`]).
    #[must_use]
    pub fn negate(&self) -> Atom {
        Atom {
            poly: self.poly.clone(),
            relation: self.relation.negate(),
        }
    }
}

/// `∃x. ⋀ᵢ atoms[i]` — the conjunctive fragment.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ExistsFormula {
    /// The conjuncts. An **empty** conjunction is `true` (witnessed at `x = 0`).
    pub atoms: Vec<Atom>,
}

impl ExistsFormula {
    /// Build `∃x. ⋀ atoms`.
    #[must_use]
    pub fn new(atoms: Vec<Atom>) -> ExistsFormula {
        ExistsFormula { atoms }
    }
}

/// `∀x. ⋁ᵢ atoms[i]` — the De Morgan dual of [`ExistsFormula`].
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ForallFormula {
    /// The disjuncts. An **empty** disjunction is `false`.
    pub atoms: Vec<Atom>,
}

impl ForallFormula {
    /// Build `∀x. ⋁ atoms`.
    #[must_use]
    pub fn new(atoms: Vec<Atom>) -> ForallFormula {
        ForallFormula { atoms }
    }

    /// The negated existential `∃x. ⋀ᵢ ¬atoms[i]`, whose refutation is exactly
    /// a proof of this universal. See [`Relation::negate`] for the table.
    #[must_use]
    pub fn negate(&self) -> ExistsFormula {
        ExistsFormula {
            atoms: self.atoms.iter().map(Atom::negate).collect(),
        }
    }
}

// ============================================================================
// Sample points.
// ============================================================================

/// A point of ℝ named exactly: either a rational, or a real algebraic number
/// given by a defining polynomial and a Sturm-isolating bracket
/// `(lower, upper]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SamplePoint {
    /// An exact rational.
    Rational(BigRational),
    /// The unique real root of `defining_poly` in `(lower, upper]`.
    Algebraic {
        /// The defining polynomial, LSB-first over ℚ.
        defining_poly: Vec<BigRational>,
        /// The bracket's lower endpoint (exclusive).
        lower: BigRational,
        /// The bracket's upper endpoint (inclusive).
        upper: BigRational,
    },
}

impl SamplePoint {
    /// The sample for one isolated root of `defining_poly`: a root recognised
    /// as rational is emitted as an exact [`SamplePoint::Rational`], anything
    /// else keeps the defining polynomial and its bracket.
    pub(crate) fn from_isolated(
        defining_poly: &[BigRational],
        root: &big::IsolatedRoot,
    ) -> SamplePoint {
        if root.exact {
            SamplePoint::Rational(root.hi.clone())
        } else {
            SamplePoint::Algebraic {
                defining_poly: defining_poly.to_vec(),
                lower: root.lo.clone(),
                upper: root.hi.clone(),
            }
        }
    }
}

// ============================================================================
// Certificates and their faults.
// ============================================================================

/// Why a certificate was refused. Every variant is a **distinct guard**;
/// [`Fault::Declined`] is the one variant that is not an accusation — it means
/// the exact arithmetic ran out of its named step budget, so the certificate
/// was neither accepted nor disproved.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Fault {
    /// The certificate records a different number of signs than the formula
    /// has conjuncts, so some `pᵢ` is unaccounted for.
    SignCountMismatch {
        /// Signs recorded in the certificate.
        recorded: usize,
        /// Conjuncts in the formula.
        atoms: usize,
    },
    /// A recorded bracket does not contain exactly one root of the recorded
    /// defining polynomial, so the "algebraic sample" names nothing.
    NotIsolating {
        /// How many distinct real roots the bracket actually contains.
        roots_in_bracket: usize,
    },
    /// A recomputed sign disagrees with the recorded one.
    SignMismatch {
        /// Index of the conjunct.
        index: usize,
        /// The sign the certificate claims.
        recorded: i8,
        /// The sign re-derived from the polynomial and the sample.
        recomputed: i8,
    },
    /// A conjunct's relation does not hold at the recomputed sign, so the
    /// sample does not satisfy the formula.
    RelationFails {
        /// Index of the conjunct.
        index: usize,
        /// The recomputed sign at which the relation fails.
        sign: i8,
    },
    /// The refutation records the wrong number of cells for its root list
    /// (`2r + 1` cells are required for `r` roots).
    CellCountMismatch {
        /// Cells recorded.
        recorded: usize,
        /// Cells required by the root list.
        expected: usize,
    },
    /// The refutation records the wrong number of open-cell samples
    /// (`r + 1` are required for `r` roots).
    OpenSampleCountMismatch {
        /// Open samples recorded.
        recorded: usize,
        /// Open samples required by the root list.
        expected: usize,
    },
    /// The cells do not cover ℝ in order: an open sample is not strictly below
    /// the next root, or not strictly above the previous one.
    CellOrderViolation {
        /// Index of the open sample that is out of place.
        index: usize,
    },
    /// The recorded root list misses a real root of some `pᵢ`, so the recorded
    /// cells are not sign-invariant and the refutation proves nothing.
    IncompleteRootList {
        /// Index of the conjunct whose roots were miscounted.
        atom: usize,
        /// Distinct real roots of that conjunct, by an independent Sturm count.
        sturm_count: usize,
        /// Recorded roots at which that conjunct vanishes.
        recorded: usize,
    },
    /// A cell names a conjunct index that the formula does not have.
    ConjunctIndexOutOfRange {
        /// The offending cell.
        cell: usize,
        /// The out-of-range index it named.
        index: usize,
    },
    /// A cell's nominated conjunct **holds** at that cell's sample, so the cell
    /// is not refuted at all.
    ConjunctDoesNotFail {
        /// The offending cell.
        cell: usize,
        /// The conjunct the cell nominated.
        index: usize,
        /// The recomputed sign, at which the relation holds.
        sign: i8,
    },
    /// A disjunctive certificate names a disjunct the formula does not have.
    DisjunctIndexOutOfRange {
        /// The index the certificate named.
        recorded: usize,
        /// How many disjuncts the formula actually has.
        disjuncts: usize,
    },
    /// A cell of a disjunctive refutation does not refute **every** disjunct:
    /// it records a different number of failing conjuncts than the formula has
    /// disjuncts. This is the guard that stops a refutation from quietly
    /// skipping one branch of the disjunction.
    DisjunctFailureCountMismatch {
        /// The offending cell.
        cell: usize,
        /// Failing conjuncts recorded in that cell.
        recorded: usize,
        /// Disjuncts the formula has.
        disjuncts: usize,
    },
    /// Exact arithmetic ran out of a named step budget. Not a refusal of the
    /// claim.
    Declined(&'static str),
}

/// Witness that `∃x. ⋀ᵢ pᵢ ▷ᵢ 0` is **true**: one point at which every
/// conjunct holds, plus the sign of every conjunct there.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SampleCertificate {
    /// The formula this certificate is about.
    pub atoms: Vec<Atom>,
    /// The satisfying point.
    pub sample: SamplePoint,
    /// `signs[i]` is the claimed sign of `atoms[i].poly` at `sample`.
    pub signs: Vec<i8>,
}

impl SampleCertificate {
    /// Re-derive the claim from `atoms` and `sample` alone.
    ///
    /// Guards, in order: every `pᵢ` has a recorded sign; the bracket of an
    /// algebraic sample really isolates one root of its defining polynomial
    /// (independent Sturm count); every recorded sign equals the recomputed
    /// one; every relation holds at the recomputed sign. Nothing the producer
    /// computed is reused — the signs are recomputed from the polynomials, by
    /// `BigRational` Horner at a rational sample and by
    /// the private `qe::big` engine (`sign_at_algebraic`) at an algebraic one.
    ///
    /// # Errors
    ///
    /// Returns the [`Fault`] naming the guard that rejected, or
    /// [`Fault::Declined`] if a step budget ran out.
    pub fn verify(&self) -> Result<(), Fault> {
        if self.signs.len() != self.atoms.len() {
            return Err(Fault::SignCountMismatch {
                recorded: self.signs.len(),
                atoms: self.atoms.len(),
            });
        }
        check_sample_is_isolated(&self.sample)?;
        check_atoms_hold(&self.atoms, &self.sample, Some(&self.signs))
    }
}

/// Every atom holds at `sample`, with the recorded signs if any are supplied.
pub(crate) fn check_atoms_hold(
    atoms: &[Atom],
    sample: &SamplePoint,
    recorded_signs: Option<&[i8]>,
) -> Result<(), Fault> {
    for (index, atom) in atoms.iter().enumerate() {
        let recomputed = sign_at_sample(&atom.poly, sample)
            .ok_or(Fault::Declined("sign at the sample point declined"))?;
        if let Some(signs) = recorded_signs {
            let recorded = signs[index];
            if recorded != recomputed {
                return Err(Fault::SignMismatch {
                    index,
                    recorded,
                    recomputed,
                });
            }
        }
        if !atom.relation.holds(recomputed) {
            return Err(Fault::RelationFails {
                index,
                sign: recomputed,
            });
        }
    }
    Ok(())
}

/// The conjunct that fails in one cell, and its sign there.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CellFailure {
    /// Index into the formula's conjuncts.
    pub conjunct: usize,
    /// The sign that conjunct's polynomial takes in this cell.
    pub sign: i8,
}

/// Witness that `∃x. ⋀ᵢ pᵢ ▷ᵢ 0` is **false**: the full sign-invariant cell
/// decomposition of ℝ, and a failing conjunct for every cell.
///
/// Cells are ordered along the line and interleaved:
///
/// ```text
/// cell 0    (−∞, α₀)      sample open_samples[0]
/// cell 1    {α₀}          sample roots[0]
/// cell 2    (α₀, α₁)      sample open_samples[1]
/// ...
/// cell 2r−1 {α_{r−1}}     sample roots[r−1]
/// cell 2r   (α_{r−1}, ∞)  sample open_samples[r]
/// ```
///
/// With no roots at all there is one cell, all of ℝ, sampled at
/// `open_samples[0]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RefutationCertificate {
    /// The formula this certificate is about.
    pub atoms: Vec<Atom>,
    /// The distinct real roots of all the `pᵢ`, strictly ascending.
    pub roots: Vec<SamplePoint>,
    /// One rational sample per open cell; `roots.len() + 1` of them.
    pub open_samples: Vec<BigRational>,
    /// One failing conjunct per cell; `2·roots.len() + 1` of them.
    pub failures: Vec<CellFailure>,
}

impl RefutationCertificate {
    /// The sample point of cell `index`, in the interleaved order documented on
    /// the struct.
    pub(crate) fn cell_sample(&self, index: usize) -> Option<SamplePoint> {
        cell_sample_of(&self.roots, &self.open_samples, index)
    }

    /// Re-derive the refutation from `atoms` alone.
    ///
    /// Guards, in order: the cell and open-sample counts match the root list;
    /// every recorded algebraic root's bracket really isolates one root; the
    /// samples and roots strictly interleave, so the cells cover ℝ in order;
    /// the root list is **complete** — for every conjunct, an independent
    /// `BigRational` Sturm count of its distinct real roots over a Cauchy bound
    /// equals the number of recorded roots at which it vanishes; and every
    /// cell's nominated conjunct has the recorded sign there and genuinely
    /// fails.
    ///
    /// Completeness is the guard that makes the decomposition sign-invariant:
    /// if no `pᵢ` has a root strictly inside an open cell, `pᵢ`'s sign is
    /// constant on that cell, so the one sample decides it.
    ///
    /// # Errors
    ///
    /// Returns the [`Fault`] naming the guard that rejected, or
    /// [`Fault::Declined`] if a step budget ran out.
    pub fn verify(&self) -> Result<(), Fault> {
        let expected_cells = 2 * self.roots.len() + 1;
        if self.failures.len() != expected_cells {
            return Err(Fault::CellCountMismatch {
                recorded: self.failures.len(),
                expected: expected_cells,
            });
        }
        check_decomposition(&self.roots, &self.open_samples, &self.atoms)?;
        self.check_every_cell_fails()
    }

    /// Every cell names a conjunct that really fails there, at the sign the
    /// certificate records.
    fn check_every_cell_fails(&self) -> Result<(), Fault> {
        for (cell, failure) in self.failures.iter().enumerate() {
            let sample = self
                .cell_sample(cell)
                .ok_or(Fault::Declined("cell index has no sample"))?;
            check_cell_failure(&self.atoms, cell, &sample, failure)?;
        }
        Ok(())
    }
}

/// The interleaved sample of cell `index`: an open sample at even indices, a
/// root at odd ones.
pub(crate) fn cell_sample_of(
    roots: &[SamplePoint],
    open_samples: &[BigRational],
    index: usize,
) -> Option<SamplePoint> {
    if index.is_multiple_of(2) {
        open_samples
            .get(index / 2)
            .cloned()
            .map(SamplePoint::Rational)
    } else {
        roots.get(index / 2).cloned()
    }
}

/// The shared decomposition guards: bracket isolation, cell order, and the
/// completeness of the root list against every polynomial in `atoms`.
///
/// Both the conjunctive refutation and the disjunctive one call this, which is
/// what keeps "the cells really are sign-invariant" a single auditable check
/// rather than two drifting copies.
pub(crate) fn check_decomposition(
    roots: &[SamplePoint],
    open_samples: &[BigRational],
    atoms: &[Atom],
) -> Result<(), Fault> {
    let expected_open = roots.len() + 1;
    if open_samples.len() != expected_open {
        return Err(Fault::OpenSampleCountMismatch {
            recorded: open_samples.len(),
            expected: expected_open,
        });
    }
    for root in roots {
        check_sample_is_isolated(root)?;
    }
    check_cell_order(roots, open_samples)?;
    check_root_list_complete(roots, atoms)
}

/// The cells cover ℝ in order: `open_samples[k] < αₖ < open_samples[k+1]`.
/// This forces the open samples to be strictly increasing *and* the roots to be
/// strictly separated by them, so no two recorded roots collide and no cell is
/// empty.
fn check_cell_order(roots: &[SamplePoint], open_samples: &[BigRational]) -> Result<(), Fault> {
    for (index, root) in roots.iter().enumerate() {
        let below = &open_samples[index];
        let above = &open_samples[index + 1];
        if compare_sample_to_rational(root, below)
            .ok_or(Fault::Declined("root/sample comparison declined"))?
            != Ordering::Greater
        {
            return Err(Fault::CellOrderViolation { index });
        }
        if compare_sample_to_rational(root, above)
            .ok_or(Fault::Declined("root/sample comparison declined"))?
            != Ordering::Less
        {
            return Err(Fault::CellOrderViolation { index: index + 1 });
        }
    }
    Ok(())
}

/// Every real root of every `pᵢ` appears in `roots`, re-checked by
/// `BigRational` Sturm counts over a Cauchy bound rather than by trusting the
/// producer's search.
fn check_root_list_complete(roots: &[SamplePoint], atoms: &[Atom]) -> Result<(), Fault> {
    for (atom_index, atom) in atoms.iter().enumerate() {
        // The zero polynomial vanishes everywhere and a nonzero constant
        // nowhere: neither can hide a missing cut point.
        let Some(sturm_count) = big::count_real_roots(&atom.poly) else {
            continue;
        };
        let mut recorded = 0usize;
        for root in roots {
            let sign = sign_at_sample(&atom.poly, root)
                .ok_or(Fault::Declined("sign at a recorded root declined"))?;
            if sign == 0 {
                recorded += 1;
            }
        }
        if sturm_count != recorded {
            return Err(Fault::IncompleteRootList {
                atom: atom_index,
                sturm_count,
                recorded,
            });
        }
    }
    Ok(())
}

/// One cell's nominated conjunct exists, has the recorded sign, and fails.
pub(crate) fn check_cell_failure(
    atoms: &[Atom],
    cell: usize,
    sample: &SamplePoint,
    failure: &CellFailure,
) -> Result<(), Fault> {
    let Some(atom) = atoms.get(failure.conjunct) else {
        return Err(Fault::ConjunctIndexOutOfRange {
            cell,
            index: failure.conjunct,
        });
    };
    let recomputed = sign_at_sample(&atom.poly, sample)
        .ok_or(Fault::Declined("sign at a cell sample declined"))?;
    if recomputed != failure.sign {
        return Err(Fault::SignMismatch {
            index: failure.conjunct,
            recorded: failure.sign,
            recomputed,
        });
    }
    if atom.relation.holds(recomputed) {
        return Err(Fault::ConjunctDoesNotFail {
            cell,
            index: failure.conjunct,
            sign: recomputed,
        });
    }
    Ok(())
}

// ============================================================================
// Decisions.
// ============================================================================

/// The verdict on an [`ExistsFormula`], with its certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Decision {
    /// Satisfiable, witnessed by a sample point.
    True(Box<SampleCertificate>),
    /// Unsatisfiable, witnessed by the cell decomposition.
    False(Box<RefutationCertificate>),
    /// Exact arithmetic declined. Never a verdict.
    Unknown(String),
}

impl Decision {
    /// Check this decision's own certificate, returning the verdict it
    /// establishes. `Ok(None)` is a decline — there is no claim to check.
    ///
    /// This is what makes a [`Decision`] a certificate-carrying answer rather
    /// than a bare verdict: nothing in it is believed until the checker has
    /// re-derived it from the polynomials.
    ///
    /// # Errors
    ///
    /// The [`Fault`] naming the guard that refused the certificate.
    pub fn verify(&self) -> Result<Option<bool>, Fault> {
        match self {
            Decision::True(cert) => cert.verify().map(|()| Some(true)),
            Decision::False(cert) => cert.verify().map(|()| Some(false)),
            Decision::Unknown(_) => Ok(None),
        }
    }
}

/// The verdict on a [`ForallFormula`]. Note the certificates swap sides: a
/// universal is *proved* by a refutation of its negation, and *refuted* by a
/// counterexample sample.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ForallDecision {
    /// Valid; the certificate refutes the negated existential.
    True(Box<RefutationCertificate>),
    /// Invalid; the certificate is a counterexample to the disjunction.
    False(Box<SampleCertificate>),
    /// Exact arithmetic declined. Never a verdict.
    Unknown(String),
}

impl ForallDecision {
    /// Check this decision's own certificate, returning the verdict it
    /// establishes. `Ok(None)` is a decline.
    ///
    /// # Errors
    ///
    /// The [`Fault`] naming the guard that refused the certificate.
    pub fn verify(&self) -> Result<Option<bool>, Fault> {
        match self {
            ForallDecision::True(cert) => cert.verify().map(|()| Some(true)),
            ForallDecision::False(cert) => cert.verify().map(|()| Some(false)),
            ForallDecision::Unknown(_) => Ok(None),
        }
    }
}

/// Decide `∃x. ⋀ᵢ pᵢ(x) ▷ᵢ 0`.
///
/// Isolates the distinct real roots of the product of the `pᵢ` in
/// `BigRational` (the private `qe::big` engine), forms the `2r + 1` sign-invariant cells,
/// and tests the conjunction at one sample per cell — the root itself for a
/// point cell, a rational strictly between consecutive roots for an open cell.
///
/// Returns [`Decision::Unknown`] with a human-readable reason only when a named
/// step budget in the private `qe::big` engine runs out. It never guesses, and it never declines for
/// an arithmetic overflow, because there is none.
#[must_use]
pub fn decide_exists(formula: &ExistsFormula) -> Decision {
    let decomposition = match decompose(&formula.atoms) {
        Ok(parts) => parts,
        Err(reason) => return Decision::Unknown(reason),
    };
    let open_samples = decomposition.open_samples;
    let root_samples: Vec<SamplePoint> = decomposition
        .roots
        .iter()
        .map(|root| SamplePoint::from_isolated(&decomposition.cut, root))
        .collect();

    let cells = 2 * root_samples.len() + 1;
    let mut failures: Vec<CellFailure> = Vec::with_capacity(cells);
    for cell in 0..cells {
        let Some(sample) = cell_sample_of(&root_samples, &open_samples, cell) else {
            return Decision::Unknown(format!("cell {cell} has no sample"));
        };
        let mut signs: Vec<i8> = Vec::with_capacity(formula.atoms.len());
        for atom in &formula.atoms {
            match sign_at_sample(&atom.poly, &sample) {
                Some(sign) => signs.push(sign),
                None => {
                    return Decision::Unknown(format!(
                        "exact sign evaluation declined in cell {cell}"
                    ));
                }
            }
        }
        match first_failure(&formula.atoms, &signs) {
            None => {
                return Decision::True(Box::new(SampleCertificate {
                    atoms: formula.atoms.clone(),
                    sample,
                    signs,
                }));
            }
            Some(failure) => failures.push(failure),
        }
    }
    Decision::False(Box::new(RefutationCertificate {
        atoms: formula.atoms.clone(),
        roots: root_samples,
        open_samples,
        failures,
    }))
}

/// Decide `∀x. ⋁ᵢ pᵢ(x) ▷ᵢ 0`, by deciding the negated existential
/// ([`ForallFormula::negate`], whose table is on [`Relation::negate`]) and
/// swapping the verdict.
#[must_use]
pub fn decide_forall(formula: &ForallFormula) -> ForallDecision {
    match decide_exists(&formula.negate()) {
        Decision::False(refutation) => ForallDecision::True(refutation),
        Decision::True(sample) => ForallDecision::False(sample),
        Decision::Unknown(reason) => ForallDecision::Unknown(reason),
    }
}

/// The thin, **self-checking** front door: decide `∃x. ⋀ᵢ pᵢ ▷ᵢ 0` and verify
/// the certificate before answering.
///
/// `Some(true)` / `Some(false)` are returned only when the corresponding
/// certificate passed its own `verify`; a decline, or a certificate this
/// module's own checker refuses, both yield `None`. Callers that want the
/// certificate itself call [`decide_exists`] and verify it themselves — this
/// function exists so that "the producer and the checker agree" is the default
/// path rather than an opt-in.
#[must_use]
pub fn eliminate(formula: &ExistsFormula) -> Option<bool> {
    decide_exists(formula).verify().unwrap_or(None)
}

/// The universal front door, dual to [`eliminate`]; likewise self-checking.
#[must_use]
pub fn eliminate_forall(formula: &ForallFormula) -> Option<bool> {
    decide_forall(formula).verify().unwrap_or(None)
}

/// The first conjunct whose relation fails at the given signs, if any.
pub(crate) fn first_failure(atoms: &[Atom], signs: &[i8]) -> Option<CellFailure> {
    for (index, atom) in atoms.iter().enumerate() {
        let sign = signs[index];
        if !atom.relation.holds(sign) {
            return Some(CellFailure {
                conjunct: index,
                sign,
            });
        }
    }
    None
}

// ============================================================================
// The decomposition (producer side).
// ============================================================================

/// The **cut polynomial**: the square-free part of the product of every
/// non-constant atom polynomial. Its distinct real roots are exactly the points
/// where some `pᵢ` changes sign, so they are exactly the cut points of the
/// sign-invariant decomposition.
///
/// Using one product rather than isolating each atom separately is what removes
/// the first slice's cross-polynomial comparison problem: the roots come out of
/// a single bisection already distinct, already ordered, and already carrying
/// pairwise disjoint brackets, so no two algebraic numbers ever have to be
/// compared.
pub(crate) fn cut_polynomial(atoms: &[Atom]) -> Vec<BigRational> {
    let mut product = vec![BigRational::one()];
    for atom in atoms {
        if big::degree(&atom.poly).is_none_or(|d| d == 0) {
            continue; // the zero polynomial or a nonzero constant: no roots
        }
        product = big::mul(&product, &atom.poly);
    }
    big::squarefree_part(&product).unwrap_or_default()
}

/// The sign-invariant decomposition of ℝ induced by a set of atoms.
#[derive(Debug, Clone)]
pub(crate) struct Decomposition {
    /// The isolated distinct real roots of the cut polynomial, ascending.
    pub(crate) roots: Vec<big::IsolatedRoot>,
    /// One rational sample per open cell; `roots.len() + 1` of them.
    pub(crate) open_samples: Vec<BigRational>,
    /// The cut polynomial, which is the defining polynomial of every algebraic
    /// root sample.
    pub(crate) cut: Vec<BigRational>,
}

/// The full decomposition of ℝ induced by `atoms`.
pub(crate) fn decompose(atoms: &[Atom]) -> Result<Decomposition, String> {
    let cut = cut_polynomial(atoms);
    let roots = if big::degree(&cut).is_none_or(|d| d == 0) {
        Vec::new()
    } else {
        big::isolate(&cut)
            .ok_or_else(|| "real-root isolation ran out of its bisection budget".to_string())?
    };
    let open_samples = open_cell_samples(&cut, &roots)?;
    Ok(Decomposition {
        roots,
        open_samples,
        cut,
    })
}

/// One rational sample strictly inside every open cell: below the first root,
/// between each consecutive pair, and above the last.
///
/// The isolating brackets are pairwise disjoint (`hiⱼ ≤ loⱼ₊₁`) and every root
/// satisfies `loⱼ < αⱼ ≤ hiⱼ`, so the separator is read straight off the
/// brackets in all but one case: when `αⱼ` is *exactly* `hiⱼ` and the next
/// bracket starts there. Only then does anything have to be searched for, and
/// then the search is a bisection of the next bracket.
fn open_cell_samples(
    cut: &[BigRational],
    roots: &[big::IsolatedRoot],
) -> Result<Vec<BigRational>, String> {
    if roots.is_empty() {
        // No root anywhere: ℝ is one cell and every point decides it.
        return Ok(vec![BigRational::zero()]);
    }
    let chain =
        big::SturmChain::new(cut).ok_or_else(|| "the cut polynomial is zero".to_string())?;
    let mut samples: Vec<BigRational> = Vec::with_capacity(roots.len() + 1);
    samples.push(roots[0].lo.clone());
    for window in roots.windows(2) {
        let (previous, next) = (&window[0], &window[1]);
        let separator = if previous.exact {
            if previous.hi < next.lo {
                next.lo.clone()
            } else {
                strictly_below_root(&chain, &next.lo, &next.hi)?
            }
        } else {
            previous.hi.clone()
        };
        samples.push(separator);
    }
    let last = roots.last().expect("roots is non-empty");
    samples.push(&last.hi + BigRational::one());
    Ok(samples)
}

/// A rational strictly greater than `lo` and strictly less than the unique root
/// of the cut polynomial in `(lo, hi]`, by bisection.
fn strictly_below_root(
    chain: &big::SturmChain,
    lo: &BigRational,
    hi: &BigRational,
) -> Result<BigRational, String> {
    let two = BigRational::from_integer(BigInt::from(2));
    let mut hi = hi.clone();
    for _ in 0..MAX_SEPARATION_STEPS {
        let mid = (lo + &hi) / &two;
        if chain.count_in(lo, &mid) == 0 {
            return Ok(mid); // the root is in (mid, hi], so lo < mid < root
        }
        hi = mid;
    }
    Err("two roots did not separate within the bisection budget".to_string())
}

// ============================================================================
// Exact sign evaluation (checker side; also used by the producer).
// ============================================================================

/// The exact sign of `poly` at a sample point: `BigRational` Horner at a
/// rational, and the private `qe::big` engine (`sign_at_algebraic`) at an algebraic one — a gcd root
/// count for the zero case, then bracket refinement until `poly` has no root in
/// the bracket at all.
pub(crate) fn sign_at_sample(poly: &[BigRational], sample: &SamplePoint) -> Option<i8> {
    match sample {
        SamplePoint::Rational(value) => Some(big::sign_at(poly, value)),
        SamplePoint::Algebraic {
            defining_poly,
            lower,
            upper,
        } => big::sign_at_algebraic(poly, defining_poly, lower, upper),
    }
}

/// Where a sample point sits relative to a rational.
pub(crate) fn compare_sample_to_rational(
    sample: &SamplePoint,
    x: &BigRational,
) -> Option<Ordering> {
    match sample {
        SamplePoint::Rational(value) => Some(value.cmp(x)),
        SamplePoint::Algebraic {
            defining_poly,
            lower,
            upper,
        } => big::compare_algebraic_to_rational(defining_poly, lower, upper, x),
    }
}

/// The guard behind every certificate's "this bracket names one real number":
/// an independent `BigRational` Sturm count over the recorded bracket must be
/// exactly one. A rational sample has nothing to isolate.
pub(crate) fn check_sample_is_isolated(sample: &SamplePoint) -> Result<(), Fault> {
    let SamplePoint::Algebraic {
        defining_poly,
        lower,
        upper,
    } = sample
    else {
        return Ok(());
    };
    let count = big::count_roots_in(defining_poly, lower, upper)
        .ok_or(Fault::Declined("Sturm count over the bracket declined"))?;
    if count == 1 {
        Ok(())
    } else {
        Err(Fault::NotIsolating {
            roots_in_bracket: count,
        })
    }
}

// ============================================================================
// Conversions to and from the `i128` rational surface.
// ============================================================================

/// The `BigRational` view of an `i128` rational. Total.
#[must_use]
pub fn big_of_rational(value: Rational) -> BigRational {
    BigRational::new(
        BigInt::from(value.numerator()),
        BigInt::from(value.denominator()),
    )
}

/// An LSB-first `i128`-rational polynomial as a `BigRational` one.
#[must_use]
pub fn big_poly(poly: &[Rational]) -> Vec<BigRational> {
    poly.iter().copied().map(big_of_rational).collect()
}

/// The `i128` rational a `BigRational` denotes, or `None` if it does not fit.
#[must_use]
pub fn rational_of_big(value: &BigRational) -> Option<Rational> {
    let numerator = i128::try_from(value.numer().clone()).ok()?;
    let denominator = i128::try_from(value.denom().clone()).ok()?;
    Some(Rational::new(numerator, denominator))
}

// ============================================================================
// The retained `i128` route (test-only, for the differential corpus).
// ============================================================================

/// The first slice's `i128` decision route, kept **only** so the new
/// `BigRational` engine can be tested against it.
///
/// It is the original producer verbatim — [`crate::algebraic::real_roots`] for
/// isolation, pairwise [`crate::real_algebraic::algebraic_cmp`] for ordering,
/// bracket refinement for the separators — retargeted to emit today's
/// `BigRational` certificates so that both routes' certificates go through
/// exactly one checker. It declines (`Decision::Unknown`) whenever the `i128`
/// arithmetic overflows, which is the wall this module was rebuilt to remove.
#[cfg(test)]
pub(crate) mod legacy_i128 {
    use super::{
        Atom, CellFailure, Decision, ExistsFormula, RefutationCertificate, SampleCertificate,
        SamplePoint, big_of_rational, first_failure, rational_of_big, sign_at_sample,
    };
    use crate::algebraic::{self, AlgebraicReal};
    use crate::real_algebraic;
    use axeyum_ir::Rational;
    use core::cmp::Ordering;
    use num_rational::BigRational;

    /// The refinement budget of the first slice, unchanged.
    const MAX_SEPARATION_STEPS: usize = 60;

    /// The `i128` polynomial an atom denotes, or `None` if a coefficient does
    /// not fit — the overflow wall, made explicit.
    fn i128_poly(poly: &[BigRational]) -> Option<Vec<Rational>> {
        poly.iter().map(rational_of_big).collect()
    }

    /// Decide `∃x. ⋀ᵢ pᵢ ▷ᵢ 0` through the `i128` machinery.
    pub(crate) fn decide_exists_i128(formula: &ExistsFormula) -> Decision {
        let mut i128_atoms: Vec<(Vec<Rational>, &Atom)> = Vec::new();
        for atom in &formula.atoms {
            match i128_poly(&atom.poly) {
                Some(poly) => i128_atoms.push((poly, atom)),
                None => {
                    return Decision::Unknown(
                        "a coefficient does not fit i128: the legacy route cannot express this"
                            .to_string(),
                    );
                }
            }
        }
        let roots = match merged_roots(&i128_atoms) {
            Ok(roots) => roots,
            Err(reason) => return Decision::Unknown(reason),
        };
        let open_samples = match open_cell_samples(&roots) {
            Ok(samples) => samples,
            Err(reason) => return Decision::Unknown(reason),
        };
        let root_samples: Vec<SamplePoint> = roots.iter().map(sample_of).collect();
        let open_samples: Vec<BigRational> =
            open_samples.into_iter().map(big_of_rational).collect();

        let cells = 2 * root_samples.len() + 1;
        let mut failures: Vec<CellFailure> = Vec::with_capacity(cells);
        for cell in 0..cells {
            let sample = if cell.is_multiple_of(2) {
                SamplePoint::Rational(open_samples[cell / 2].clone())
            } else {
                root_samples[cell / 2].clone()
            };
            let mut signs: Vec<i8> = Vec::with_capacity(formula.atoms.len());
            for atom in &formula.atoms {
                match sign_at_sample(&atom.poly, &sample) {
                    Some(sign) => signs.push(sign),
                    None => {
                        return Decision::Unknown(format!(
                            "exact sign evaluation declined in cell {cell}"
                        ));
                    }
                }
            }
            match first_failure(&formula.atoms, &signs) {
                None => {
                    return Decision::True(Box::new(SampleCertificate {
                        atoms: formula.atoms.clone(),
                        sample,
                        signs,
                    }));
                }
                Some(failure) => failures.push(failure),
            }
        }
        Decision::False(Box::new(RefutationCertificate {
            atoms: formula.atoms.clone(),
            roots: root_samples,
            open_samples,
            failures,
        }))
    }

    /// The `SamplePoint` an `i128` isolated root denotes.
    fn sample_of(root: &AlgebraicReal) -> SamplePoint {
        if let Some(value) = root.rational_value() {
            return SamplePoint::Rational(big_of_rational(value));
        }
        let (lower, upper) = root.isolating_interval();
        SamplePoint::Algebraic {
            defining_poly: super::big_poly(root.minimal_polynomial()),
            lower: big_of_rational(lower),
            upper: big_of_rational(upper),
        }
    }

    /// Every distinct real root of every conjunct, strictly ascending.
    fn merged_roots(atoms: &[(Vec<Rational>, &Atom)]) -> Result<Vec<AlgebraicReal>, String> {
        let mut roots: Vec<AlgebraicReal> = Vec::new();
        for (index, (poly, _)) in atoms.iter().enumerate() {
            if axeyum_ir::poly::rat_degree(poly).unwrap_or(0) == 0 {
                continue;
            }
            let Some(found) = algebraic::real_roots(poly) else {
                return Err(format!(
                    "real-root isolation declined for conjunct {index} (overflow or a degree cap)"
                ));
            };
            for root in found {
                let mut duplicate = false;
                for existing in &roots {
                    match compare_roots(existing, &root) {
                        Some(Ordering::Equal) => {
                            duplicate = true;
                            break;
                        }
                        Some(_) => {}
                        None => {
                            return Err(format!(
                                "exact comparison of two algebraic roots declined (conjunct {index})"
                            ));
                        }
                    }
                }
                if !duplicate {
                    roots.push(root);
                }
            }
        }
        let mut sorted: Vec<AlgebraicReal> = Vec::with_capacity(roots.len());
        for root in roots {
            let mut position = sorted.len();
            for (index, existing) in sorted.iter().enumerate() {
                match compare_roots(&root, existing) {
                    Some(Ordering::Less) => {
                        position = index;
                        break;
                    }
                    Some(_) => {}
                    None => {
                        return Err("exact comparison of two algebraic roots declined".to_string());
                    }
                }
            }
            sorted.insert(position, root);
        }
        Ok(sorted)
    }

    /// Exact comparison of two isolated real roots.
    fn compare_roots(a: &AlgebraicReal, b: &AlgebraicReal) -> Option<Ordering> {
        if let (Some(x), Some(y)) = (a.rational_value(), b.rational_value()) {
            return x.checked_cmp(&y);
        }
        let (a_lo, a_hi) = a.isolating_interval();
        let (b_lo, b_hi) = b.isolating_interval();
        if a_hi.checked_cmp(&b_lo)? != Ordering::Greater {
            return Some(Ordering::Less);
        }
        if b_hi.checked_cmp(&a_lo)? != Ordering::Greater {
            return Some(Ordering::Greater);
        }
        if a.minimal_polynomial() == b.minimal_polynomial() && a_lo == b_lo && a_hi == b_hi {
            return Some(Ordering::Equal);
        }
        let left = real_algebraic::from_algebraic_real(a)?;
        let right = real_algebraic::from_algebraic_real(b)?;
        real_algebraic::algebraic_cmp(&left, &right)
    }

    /// One rational sample strictly inside every open cell.
    fn open_cell_samples(roots: &[AlgebraicReal]) -> Result<Vec<Rational>, String> {
        if roots.is_empty() {
            return Ok(vec![Rational::zero()]);
        }
        let mut samples: Vec<Rational> = Vec::with_capacity(roots.len() + 1);
        let mut lowest = roots[0].isolating_interval().0;
        let mut highest = roots[0].isolating_interval().1;
        for root in roots {
            let (lo, hi) = root.isolating_interval();
            if lo
                .checked_cmp(&lowest)
                .ok_or("bracket comparison overflowed")?
                == Ordering::Less
            {
                lowest = lo;
            }
            if hi
                .checked_cmp(&highest)
                .ok_or("bracket comparison overflowed")?
                == Ordering::Greater
            {
                highest = hi;
            }
        }
        samples.push(
            lowest
                .checked_sub(Rational::integer(1))
                .ok_or("left-hand sample overflowed")?,
        );
        for window in roots.windows(2) {
            samples.push(rational_between(&window[0], &window[1])?);
        }
        samples.push(
            highest
                .checked_add(Rational::integer(1))
                .ok_or("right-hand sample overflowed")?,
        );
        Ok(samples)
    }

    /// A rational strictly between two consecutive roots `a < b`.
    fn rational_between(a: &AlgebraicReal, b: &AlgebraicReal) -> Result<Rational, String> {
        let mut left = a.clone();
        let mut right = b.clone();
        let mut width = Rational::integer(1);
        for _ in 0..MAX_SEPARATION_STEPS {
            let left_hi = left.isolating_interval().1;
            let right_lo = right.isolating_interval().0;
            if left_hi
                .checked_cmp(&right_lo)
                .ok_or("bracket comparison overflowed")?
                == Ordering::Less
            {
                let sum = left_hi
                    .checked_add(right_lo)
                    .ok_or("gap midpoint overflowed")?;
                return sum
                    .checked_div(Rational::integer(2))
                    .ok_or_else(|| "gap midpoint overflowed".to_string());
            }
            width = width
                .checked_div(Rational::integer(2))
                .ok_or("refinement width overflowed")?;
            left = left
                .refine(width)
                .ok_or("bracket refinement declined (i128 overflow)")?;
            right = right
                .refine(width)
                .ok_or("bracket refinement declined (i128 overflow)")?;
        }
        Err("two roots did not separate within the refinement budget".to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::legacy_i128::decide_exists_i128;
    use super::*;

    /// An integer-coefficient polynomial, LSB-first.
    pub(crate) fn ipoly(coeffs: &[i64]) -> Vec<BigRational> {
        integer_poly(coeffs)
    }

    /// The rational `n/d`.
    fn frac(n: i64, d: i64) -> BigRational {
        BigRational::new(BigInt::from(n), BigInt::from(d))
    }

    /// The integer `n` as a `BigRational`.
    pub(crate) fn int(n: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(n))
    }

    /// `x`, LSB-first.
    fn x_poly() -> Vec<BigRational> {
        ipoly(&[0, 1])
    }

    fn exists(atoms: Vec<Atom>) -> ExistsFormula {
        ExistsFormula::new(atoms)
    }

    fn as_true(decision: Decision) -> SampleCertificate {
        match decision {
            Decision::True(cert) => *cert,
            other => panic!("expected True, got {other:?}"),
        }
    }

    fn as_false(decision: Decision) -> RefutationCertificate {
        match decision {
            Decision::False(cert) => *cert,
            other => panic!("expected False, got {other:?}"),
        }
    }

    // ---------------------------------------------------------------- table

    #[test]
    fn relation_negation_is_an_involution_and_flips_every_sign_verdict() {
        for relation in [
            Relation::Eq,
            Relation::Ne,
            Relation::Lt,
            Relation::Le,
            Relation::Gt,
            Relation::Ge,
        ] {
            assert_eq!(relation.negate().negate(), relation);
            for sign in [-1i8, 0, 1] {
                assert_ne!(
                    relation.holds(sign),
                    relation.negate().holds(sign),
                    "{relation:?} at sign {sign}"
                );
            }
        }
    }

    // ------------------------------------------------------------- verdicts

    #[test]
    fn exists_x_squared_minus_two_equals_zero_is_true_at_an_algebraic_sample() {
        let formula = exists(vec![Atom::new(ipoly(&[-2, 0, 1]), Relation::Eq)]);
        let cert = as_true(decide_exists(&formula));
        assert!(
            matches!(cert.sample, SamplePoint::Algebraic { .. }),
            "sqrt(2) is irrational, so the sample must be algebraic: {:?}",
            cert.sample
        );
        assert_eq!(cert.signs, vec![0]);
        assert_eq!(cert.verify(), Ok(()));
        assert_eq!(eliminate(&formula), Some(true));
    }

    #[test]
    fn exists_x_squared_plus_one_negative_is_false_with_a_single_whole_line_cell() {
        let formula = exists(vec![Atom::new(ipoly(&[1, 0, 1]), Relation::Lt)]);
        let cert = as_false(decide_exists(&formula));
        // `x² + 1` has no real root, so the sign-invariant decomposition of ℝ
        // is one cell, not two: there is nothing to cut the line at.
        assert!(cert.roots.is_empty());
        assert_eq!(cert.open_samples.len(), 1);
        assert_eq!(cert.failures.len(), 1);
        assert_eq!(cert.failures[0].conjunct, 0);
        assert_eq!(cert.failures[0].sign, 1);
        assert_eq!(cert.verify(), Ok(()));
        assert_eq!(eliminate(&formula), Some(false));
    }

    #[test]
    fn exists_x_squared_lt_two_and_x_gt_one_is_true_at_a_rational_sample() {
        let formula = exists(vec![
            Atom::new(ipoly(&[-2, 0, 1]), Relation::Lt),
            Atom::new(ipoly(&[-1, 1]), Relation::Gt),
        ]);
        let cert = as_true(decide_exists(&formula));
        let SamplePoint::Rational(sample) = cert.sample.clone() else {
            panic!("the satisfying cell is open, so the sample is rational");
        };
        // Strictly between 1 and sqrt(2).
        assert_eq!(big::sign_at(&ipoly(&[-1, 1]), &sample), 1);
        assert_eq!(big::sign_at(&ipoly(&[-2, 0, 1]), &sample), -1);
        assert_eq!(cert.signs, vec![-1, 1]);
        assert_eq!(cert.verify(), Ok(()));
    }

    #[test]
    fn exists_cubic_root_strictly_inside_the_unit_interval_is_false_at_the_point_cell_on_one() {
        // ∃x. x³ − x = 0 ∧ x > 0 ∧ x < 1.  The only positive root is 1, which
        // the strict upper bound excludes.
        let formula = exists(vec![
            Atom::new(ipoly(&[0, -1, 0, 1]), Relation::Eq),
            Atom::new(x_poly(), Relation::Gt),
            Atom::new(ipoly(&[-1, 1]), Relation::Lt),
        ]);
        let cert = as_false(decide_exists(&formula));
        assert_eq!(
            cert.roots,
            vec![
                SamplePoint::Rational(int(-1)),
                SamplePoint::Rational(int(0)),
                SamplePoint::Rational(int(1)),
            ]
        );
        assert_eq!(cert.failures.len(), 7);
        // Cell 5 is the point cell {1}: `x − 1` has sign 0 there, so `x < 1`
        // is the conjunct that fails.
        assert_eq!(
            cert.failures[5],
            CellFailure {
                conjunct: 2,
                sign: 0
            }
        );
        assert_eq!(cert.verify(), Ok(()));
        assert_eq!(eliminate(&formula), Some(false));
    }

    #[test]
    fn forall_x_squared_nonnegative_is_true() {
        let formula = ForallFormula::new(vec![Atom::new(ipoly(&[0, 0, 1]), Relation::Ge)]);
        let ForallDecision::True(cert) = decide_forall(&formula) else {
            panic!("x² ≥ 0 is valid");
        };
        assert_eq!(cert.roots, vec![SamplePoint::Rational(int(0))]);
        assert_eq!(cert.failures.len(), 3);
        assert_eq!(cert.verify(), Ok(()));
        assert_eq!(eliminate_forall(&formula), Some(true));
    }

    #[test]
    fn forall_x_squared_minus_x_nonnegative_is_false_with_a_counterexample_below_one() {
        let formula = ForallFormula::new(vec![Atom::new(ipoly(&[0, -1, 1]), Relation::Ge)]);
        let ForallDecision::False(cert) = decide_forall(&formula) else {
            panic!("x² − x < 0 on (0, 1), so the universal is false");
        };
        let SamplePoint::Rational(sample) = cert.sample.clone() else {
            panic!("the counterexample cell (0, 1) is open");
        };
        assert_eq!(big::sign_at(&x_poly(), &sample), 1, "sample > 0");
        assert_eq!(big::sign_at(&ipoly(&[-1, 1]), &sample), -1, "sample < 1");
        assert_eq!(cert.verify(), Ok(()));
        assert_eq!(eliminate_forall(&formula), Some(false));
    }

    #[test]
    fn exists_double_root_case_is_true_at_the_double_root_as_a_point_cell() {
        // (x−1)²·(x−2) = x³ − 4x² + 5x − 2 ≥ 0 ∧ x < 3/2.  The only point where
        // the cubic is non-negative below 3/2 is the double root x = 1.
        let cubic = ipoly(&[-2, 5, -4, 1]);
        let bound = vec![frac(-3, 2), int(1)];
        let formula = exists(vec![
            Atom::new(cubic, Relation::Ge),
            Atom::new(bound, Relation::Lt),
        ]);
        let cert = as_true(decide_exists(&formula));
        assert_eq!(cert.sample, SamplePoint::Rational(int(1)));
        assert_eq!(cert.signs, vec![0, -1]);
        assert_eq!(cert.verify(), Ok(()));
    }

    // ------------------------------------------------------- forged samples

    #[test]
    fn forged_sample_certificate_with_a_missing_conjunct_sign_is_refused() {
        let atoms = vec![Atom::new(x_poly(), Relation::Gt)];
        let cert = SampleCertificate {
            atoms,
            sample: SamplePoint::Rational(int(1)),
            signs: Vec::new(),
        };
        assert_eq!(
            cert.verify(),
            Err(Fault::SignCountMismatch {
                recorded: 0,
                atoms: 1
            })
        );
    }

    #[test]
    fn forged_sample_certificate_with_a_wrong_sign_is_refused() {
        let formula = exists(vec![Atom::new(ipoly(&[-2, 0, 1]), Relation::Lt)]);
        let mut cert = as_true(decide_exists(&formula));
        assert_eq!(cert.verify(), Ok(()));
        cert.signs[0] = 1;
        assert_eq!(
            cert.verify(),
            Err(Fault::SignMismatch {
                index: 0,
                recorded: 1,
                recomputed: -1
            })
        );
        // The same forgery must not survive the front door either: a
        // `Decision` is only as good as the certificate it carries.
        assert_eq!(
            Decision::True(Box::new(cert)).verify(),
            Err(Fault::SignMismatch {
                index: 0,
                recorded: 1,
                recomputed: -1
            })
        );
    }

    #[test]
    fn forged_sample_certificate_whose_bracket_holds_two_roots_is_refused() {
        // (−2, 2] holds both roots of x² − 2, so it isolates nothing.
        let cert = SampleCertificate {
            atoms: vec![Atom::new(ipoly(&[-2, 0, 1]), Relation::Eq)],
            sample: SamplePoint::Algebraic {
                defining_poly: ipoly(&[-2, 0, 1]),
                lower: int(-2),
                upper: int(2),
            },
            signs: vec![0],
        };
        assert_eq!(
            cert.verify(),
            Err(Fault::NotIsolating {
                roots_in_bracket: 2
            })
        );
    }

    #[test]
    fn forged_sample_certificate_whose_relation_does_not_hold_is_refused() {
        // The sign is recorded correctly; the point simply does not satisfy `x > 0`.
        let cert = SampleCertificate {
            atoms: vec![Atom::new(x_poly(), Relation::Gt)],
            sample: SamplePoint::Rational(int(-1)),
            signs: vec![-1],
        };
        assert_eq!(
            cert.verify(),
            Err(Fault::RelationFails { index: 0, sign: -1 })
        );
    }

    // --------------------------------------------------- forged refutations

    /// The valid refutation of `∃x. x³ − x = 0 ∧ x > 0 ∧ x < 1`, with roots
    /// `−1 < 0 < 1` and seven cells — the fixture the forgeries below mutate.
    fn cubic_refutation() -> RefutationCertificate {
        let formula = exists(vec![
            Atom::new(ipoly(&[0, -1, 0, 1]), Relation::Eq),
            Atom::new(x_poly(), Relation::Gt),
            Atom::new(ipoly(&[-1, 1]), Relation::Lt),
        ]);
        let cert = as_false(decide_exists(&formula));
        assert_eq!(cert.verify(), Ok(()));
        cert
    }

    #[test]
    fn forged_refutation_with_a_sample_outside_its_cell_is_refused() {
        let mut cert = cubic_refutation();
        // open_samples[1] must lie in (−1, 0); 5 lies above every root, so the
        // cells no longer cover ℝ in order.
        cert.open_samples[1] = int(5);
        assert_eq!(cert.verify(), Err(Fault::CellOrderViolation { index: 1 }));
    }

    #[test]
    fn forged_refutation_that_drops_a_root_is_refused_as_an_incomplete_root_list() {
        let cert = cubic_refutation();
        // Drop the root at 0 together with its point cell, keeping every count
        // self-consistent and every remaining cell genuinely failing — only the
        // Sturm completeness recount can catch this.
        let forged = RefutationCertificate {
            atoms: cert.atoms.clone(),
            roots: vec![cert.roots[0].clone(), cert.roots[2].clone()],
            open_samples: vec![
                cert.open_samples[0].clone(),
                cert.open_samples[1].clone(),
                cert.open_samples[3].clone(),
            ],
            failures: vec![
                cert.failures[0],
                cert.failures[1],
                cert.failures[2],
                cert.failures[5],
                cert.failures[6],
            ],
        };
        assert_eq!(
            forged.verify(),
            Err(Fault::IncompleteRootList {
                atom: 0,
                sturm_count: 3,
                recorded: 2
            })
        );
    }

    #[test]
    fn forged_refutation_naming_a_conjunct_that_actually_holds_is_refused() {
        let mut cert = cubic_refutation();
        // In cell 0 (far left of every root) `x < 1` holds, so nominating it as
        // the failing conjunct — with its true sign — is a forgery.
        let sample = SamplePoint::Rational(cert.open_samples[0].clone());
        let sign = sign_at_sample(&cert.atoms[2].poly, &sample).expect("exact sign");
        cert.failures[0] = CellFailure { conjunct: 2, sign };
        assert_eq!(
            cert.verify(),
            Err(Fault::ConjunctDoesNotFail {
                cell: 0,
                index: 2,
                sign
            })
        );
    }

    #[test]
    fn forged_refutation_with_a_wrong_cell_sign_is_refused() {
        let mut cert = cubic_refutation();
        cert.failures[0] = CellFailure {
            conjunct: cert.failures[0].conjunct,
            sign: -cert.failures[0].sign,
        };
        assert!(
            matches!(cert.verify(), Err(Fault::SignMismatch { .. })),
            "a flipped cell sign must be caught by the recount"
        );
    }

    #[test]
    fn forged_refutation_naming_a_conjunct_the_formula_does_not_have_is_refused() {
        let mut cert = cubic_refutation();
        cert.failures[0] = CellFailure {
            conjunct: 99,
            sign: 0,
        };
        assert_eq!(
            cert.verify(),
            Err(Fault::ConjunctIndexOutOfRange { cell: 0, index: 99 })
        );
    }

    #[test]
    fn forged_refutation_with_the_wrong_number_of_cells_is_refused() {
        let mut cert = cubic_refutation();
        cert.failures.pop();
        assert_eq!(
            cert.verify(),
            Err(Fault::CellCountMismatch {
                recorded: 6,
                expected: 7
            })
        );
    }

    #[test]
    fn forged_refutation_with_the_wrong_number_of_open_samples_is_refused() {
        let mut cert = cubic_refutation();
        cert.open_samples.pop();
        assert_eq!(
            cert.verify(),
            Err(Fault::OpenSampleCountMismatch {
                recorded: 3,
                expected: 4
            })
        );
    }

    #[test]
    fn decision_verify_delegates_to_its_certificate_and_a_decline_carries_no_claim() {
        let formula = exists(vec![Atom::new(x_poly(), Relation::Gt)]);
        assert_eq!(decide_exists(&formula).verify(), Ok(Some(true)));
        let unsatisfiable = exists(vec![Atom::new(ipoly(&[1, 0, 1]), Relation::Lt)]);
        assert_eq!(decide_exists(&unsatisfiable).verify(), Ok(Some(false)));
        assert_eq!(
            Decision::Unknown("declined".to_string()).verify(),
            Ok(None),
            "a decline carries no claim, so there is nothing to check"
        );
    }

    // ----------------------------------------- the i128 wall, and its removal

    /// `10³⁰` and `10⁶⁰` as `BigRational`s.
    fn power_of_ten(exponent: u32) -> BigRational {
        BigRational::from_integer(BigInt::from(10u32).pow(exponent))
    }

    #[test]
    fn the_coefficient_that_defeated_the_first_slice_now_decides() {
        // `x² − 10³⁰ = 0` fits `i128` as a coefficient, but the first slice's
        // reused Sturm machinery evaluates near the Cauchy bound and overflowed
        // there, so this shape was documented as a decline. It decides now.
        let formula = exists(vec![Atom::new(
            vec![-power_of_ten(30), int(0), int(1)],
            Relation::Eq,
        )]);
        let cert = as_true(decide_exists(&formula));
        assert_eq!(
            cert.sample,
            SamplePoint::Rational(-power_of_ten(15)),
            "the root is exactly −10¹⁵ and must be recognised as rational"
        );
        assert_eq!(cert.verify(), Ok(()));
        assert_eq!(eliminate(&formula), Some(true));

        // The legacy route is the control: it still declines on this input, so
        // the test measures the new engine and not a change of subject.
        assert!(
            matches!(decide_exists_i128(&formula), Decision::Unknown(_)),
            "the i128 route must still decline, or this test proves nothing"
        );
    }

    #[test]
    fn a_coefficient_far_beyond_i128_decides_too() {
        // `x² − 10⁶⁰ > 0` cannot even be *expressed* over `i128` rationals.
        let formula = exists(vec![
            Atom::new(vec![-power_of_ten(60), int(0), int(1)], Relation::Eq),
            Atom::new(ipoly(&[0, 1]), Relation::Gt),
        ]);
        let cert = as_true(decide_exists(&formula));
        assert_eq!(cert.sample, SamplePoint::Rational(power_of_ten(30)));
        assert_eq!(cert.verify(), Ok(()));
        assert_eq!(eliminate(&formula), Some(true));

        // And the unsatisfiable companion, so the huge-coefficient path is
        // exercised on both verdicts.
        let unsatisfiable = exists(vec![
            Atom::new(vec![power_of_ten(60), int(0), int(1)], Relation::Eq),
            Atom::new(ipoly(&[0, 1]), Relation::Gt),
        ]);
        assert_eq!(eliminate(&unsatisfiable), Some(false));
    }

    /// The whole first-slice corpus, as formulas — the population the two
    /// routes are compared on.
    fn first_slice_corpus() -> Vec<(&'static str, ExistsFormula)> {
        vec![
            (
                "x² − 2 = 0",
                exists(vec![Atom::new(ipoly(&[-2, 0, 1]), Relation::Eq)]),
            ),
            (
                "x² + 1 < 0",
                exists(vec![Atom::new(ipoly(&[1, 0, 1]), Relation::Lt)]),
            ),
            (
                "x² < 2 ∧ x > 1",
                exists(vec![
                    Atom::new(ipoly(&[-2, 0, 1]), Relation::Lt),
                    Atom::new(ipoly(&[-1, 1]), Relation::Gt),
                ]),
            ),
            (
                "x³ − x = 0 ∧ x > 0 ∧ x < 1",
                exists(vec![
                    Atom::new(ipoly(&[0, -1, 0, 1]), Relation::Eq),
                    Atom::new(x_poly(), Relation::Gt),
                    Atom::new(ipoly(&[-1, 1]), Relation::Lt),
                ]),
            ),
            (
                "x² < 0 (the negated ∀x. x² ≥ 0)",
                exists(vec![Atom::new(ipoly(&[0, 0, 1]), Relation::Lt)]),
            ),
            (
                "x² − x < 0 (the negated ∀x. x² − x ≥ 0)",
                exists(vec![Atom::new(ipoly(&[0, -1, 1]), Relation::Lt)]),
            ),
            (
                "(x−1)²(x−2) ≥ 0 ∧ x < 3/2",
                exists(vec![
                    Atom::new(ipoly(&[-2, 5, -4, 1]), Relation::Ge),
                    Atom::new(vec![frac(-3, 2), int(1)], Relation::Lt),
                ]),
            ),
            ("x > 0", exists(vec![Atom::new(x_poly(), Relation::Gt)])),
            ("the empty conjunction", exists(Vec::new())),
            (
                "a constant conjunct: 1 = 0",
                exists(vec![Atom::new(ipoly(&[1]), Relation::Eq)]),
            ),
            (
                "the zero polynomial: 0 = 0",
                exists(vec![Atom::new(ipoly(&[0]), Relation::Eq)]),
            ),
        ]
    }

    #[test]
    fn the_big_rational_route_agrees_with_the_i128_route_on_the_first_slice_corpus() {
        let corpus = first_slice_corpus();
        assert_eq!(corpus.len(), 11, "the corpus must not silently shrink");
        let mut compared = 0usize;
        for (name, formula) in corpus {
            let modern = decide_exists(&formula);
            let legacy = decide_exists_i128(&formula);
            let modern_verdict = modern.verify().unwrap_or_else(|fault| {
                panic!("{name}: the new route's certificate was refused: {fault:?}")
            });
            let legacy_verdict = legacy.verify().unwrap_or_else(|fault| {
                panic!("{name}: the legacy certificate was refused: {fault:?}")
            });
            assert!(
                modern_verdict.is_some(),
                "{name}: the BigRational route must not decline"
            );
            // The legacy route may decline; where it answers, the answers must
            // agree — and its certificate must satisfy today's checker, which
            // is the stronger of the two claims.
            if let Some(legacy_verdict) = legacy_verdict {
                assert_eq!(
                    modern_verdict,
                    Some(legacy_verdict),
                    "{name}: the two routes disagree"
                );
                compared += 1;
            }
        }
        assert!(
            compared >= 9,
            "the legacy route answered only {compared} of the corpus; the comparison is too thin"
        );
    }
}
